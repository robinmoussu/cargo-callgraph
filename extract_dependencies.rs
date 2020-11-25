use bit_vec::BitVec;
use itertools::Itertools;
use rustc_hir::def;
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::terminator::*;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::symbol::Symbol;
use std::collections::HashMap;
use std::collections::HashSet;
use std::default::default;
use std::fmt;

// ************************************************************ //
// The output of the analysis

type LocalCallee = usize;

/// Store all the dependencies between one function and its callee
#[derive(Debug, Clone)]
pub struct FunctionDependencies<'tcx> {
    /// name and type of the returned value and all the arguments to this function
    arguments_name_and_type: IndexVec<mir::Local, (Option<Symbol>, ty::Ty<'tcx>)>,
    /// List of all call-sites inside the body of this function
    callees: IndexVec<LocalCallee, Callee<'tcx>>,
}

/// Store the name of a called function and the source of all of its arguments
#[derive(Debug, Clone)]
pub struct Callee<'tcx> {
    /// name of the called function
    name: mir::Operand<'tcx>, // FIXME: it should be Constant
    /// source (possibly over-approximated) of the source of the arguments to
    /// this called function
    arguments_source: Vec<Origin<'tcx>>,
}

/// Express one of the possible source of a given argument
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Origin<'tcx> {
    /// A literal expression
    Literal(ty::Const<'tcx>), // FIXME: it should probably be Const
    /// An argument of the function being analyzed
    FromArgument(mir::Local),
    /// The return value of a another callee
    FromReturn(mir::Local),
}

// ************************************************************ //
// Extract relationship between all the locals in a function

fn extract_constant<'tcx>(mir: &mir::Body<'tcx>) -> HashSet<ty::Const<'tcx>> {
    use mir::visit::Visitor;

    #[derive(Default)]
    struct Constants<'tcx> {
        constants: HashSet<ty::Const<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Constants<'tcx> {
        fn visit_constant(&mut self, constant: &mir::Constant<'tcx>, _: mir::Location) {
            self.constants.insert(constant.literal.clone());
        }
    }

    let mut search_constants = Constants::default();
    search_constants.visit_body(mir);

    search_constants.constants
}

#[derive(Debug, Clone)]
struct Dependencies<'tcx> {
    pub dependencies: IndexVec<mir::Local, BitVec>,
    pub constants: Vec<ty::Const<'tcx>>,
    pub locals_count: usize,
}
fn direct_dependencies<'mir, 'tcx>(mir: &'mir mir::Body<'tcx>) -> Dependencies<'tcx> {
    use mir::visit::Visitor;

    // A variable can depends from other locals or from constants
    // The bits in `dependencies` represent a dependency to
    //  - the return value
    //  - the arguments of the function
    //  - the local variables
    //  - temporaries
    //  - constants
    // The index of a dependency to a constant is its index in `constants` shifted by
    // `locals_count`.
    let locals_count = mir.local_decls.len();
    let constants: Vec<ty::Const> = extract_constant(mir).into_iter().collect();
    let mut dependencies = IndexVec::from_elem_n(
        BitVec::from_elem(locals_count + constants.len(), false),
        locals_count);

    struct Assignments<'tcx, 'local> {
        locals_count: usize,
        constants: &'local Vec<ty::Const<'tcx>>,
        dependencies: &'local mut IndexVec<mir::Local, BitVec>,
    }
    impl<'tcx, 'local> Assignments<'tcx, 'local> {
        fn new(
            locals_count: usize,
            constants: &'local Vec<ty::Const<'tcx>>,
            dependencies: &'local mut IndexVec<mir::Local, BitVec>,
        ) -> Self {
            Assignments {
                constants,
                dependencies,
                locals_count,
            }
        }
    }
    impl<'tcx, 'local> Visitor<'tcx> for Assignments<'tcx, 'local> {
        fn visit_assign(
            &mut self,
            lvalue: &mir::Place<'tcx>,
            rvalue: &mir::Rvalue<'tcx>,
            _: mir::Location)
        {
            let lvalue = lvalue.local;

            let constants = self.constants;
            let locals_count = self.locals_count;
            let dependencies: &mut IndexVec<mir::Local, BitVec> = self.dependencies;

            let get_id = |op: &mir::Operand<'tcx>| -> usize {
                use mir::Operand::*;
                match op {
                    Copy(place) | Move(place) => {
                        place.local.as_usize()
                    },
                    Constant(constant) => {
                        locals_count + constants.iter().position(|cst| cst == constant.literal).unwrap()
                    },
                }
            };

            use mir::Rvalue::*;
            match rvalue {
                Use(op) | Repeat(op, _) | Cast(_, op, _) | UnaryOp(_, op) => {
                    dependencies[lvalue].set(get_id(op), true);
                },
                Ref(_, _, place) | AddressOf(_, place) | Len(place) | Discriminant(place) => {
                    dependencies[lvalue].set(place.local.as_usize(), true);
                },
                ThreadLocalRef(_) => {
                    () // TODO:add support to threadlocal
                },
                BinaryOp(_, op1, op2) | CheckedBinaryOp(_, op1, op2) => {
                    dependencies[lvalue].set(get_id(op1), true);
                    dependencies[lvalue].set(get_id(op2), true);
                },
                NullaryOp(_, _) => {
                    () // no dependencies
                },
                Aggregate(_, ops) => {
                    for op in ops {
                        dependencies[lvalue].set(get_id(op), true);
                    }
                },
            }
        }
    }

    let mut search_constants = Assignments::new(locals_count, &constants, &mut dependencies);
    search_constants.visit_body(mir);

    Dependencies {
        dependencies,
        constants,
        locals_count,
    }
}

fn propagate_dependencies<'tcx>(deps: Dependencies<'tcx>) -> Dependencies<'tcx> {
    let Dependencies { mut dependencies, constants, locals_count } = deps;

    // Propagate all dependencies
    //
    // Example:
    //
    // Lets imagine that we have a function with 6 locals (return value +
    // arguments + compiler generated constant) and two constants with the
    // following maxtrix of direct dependencies where a cross means that the
    // local has a value that was set from the value of the associated
    // dependency.
    //
    //       | dependencies
    // local | _0 | _1 | _2 | _3 | _4 | _5 | cst1 | cst2
    // ------|----|----|----|----|----|----|------|------
    //   _0  |    |    |    |  X |    |    |      |
    //   _1  |    |    |    |    |    |    |      |
    //   _2  |    |    |    |  X |    |    |      |  X
    //   _3  |    |  X |  X |    |    |    |      |
    //   _4  |    |    |    |    |    |    |  X   |
    //   _5  |    |    |    |    |  X |    |      |
    //
    // The local _0 depends from _3. This means that it indirectly depends from
    // the dependencies of _3 (_1 and _2) and transitively from the dependencies
    // of _1 (none) and _2 (_3 and cst2). Since _3 was already visited, this
    // will not change anything. In conclusion _0 depends from _1, _2, _3 and
    // cst2.
    //
    // After applying the same logic for all local, the matrix of dependencies
    // becomes:
    //
    //       | dependencies
    // local | _0 | _1 | _2 | _3 | _4 | _5 | cst1 | cst2
    // ------|----|----|----|----|----|----|------|------
    //   _0  |    |  X |  X |  X |    |    |      |  X
    //   _1  |    |    |    |    |    |    |      |
    //   _2  |    |  X |  X |  X |    |    |      |  X
    //   _3  |    |  X |  X |  X |    |    |      |  X
    //   _4  |    |    |    |    |    |    |  X   |
    //   _5  |    |    |    |    |  X |    |  X   |

    let mut previous_iteration = BitVec::from_elem(locals_count + constants.len(), false);
    // FIXME: find better name for deps1 and deps2
    // deps1 and deps2 are refs to a BitVec of dependencies
    // FIXME: is there a better way to do it than this bubblesort-like algorithm?

    for index in 0..dependencies.len() {
        // Safely extract a mutable reference from the dependency list, then iterate (imutably
        // of the other dependencies
        let (left, rest) = dependencies.raw.split_at_mut(index);
        let (deps1, right) = rest.split_first_mut().unwrap();
        let other_dependencies = Iterator::chain(
            left.iter().enumerate(),
            right.iter().enumerate().map(|(i, x)| (i + 1, x)));

        loop {
            // reuse the same BitVec at each iteration to avoid useless
            // allocations
            previous_iteration.clear();
            previous_iteration.or(deps1);

            for (index, deps2) in other_dependencies.clone() {
                if deps1[index] {
                    deps1.or(deps2);
                }
            }

            // continue until we hit a stable point
            if deps1 == &previous_iteration {
                break;
            }
        }
    }
    Dependencies { dependencies, constants, locals_count }
}

// ************************************************************ //
// Utilities

#[derive(Debug, Eq, PartialEq, Ord, PartialOrd, Clone, Hash)]
struct Module(String);

impl Module {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Return the name of the module of a given function
fn get_module(tcx: ty::TyCtxt<'_>, function: DefId) -> Module {
    use ty::DefIdTree;

    let mut current = function;
    // The immediate parent might not always be a module.
    // Find the first parent which is.
    let module = loop {
        if let Some(parent) = tcx.parent(current) {
            if tcx.def_kind(parent) == rustc_hir::def::DefKind::Mod {
                break Some(parent);
            }
            current = parent;
        } else {
            debug!(
                "{:?} has no parent (kind={:?}, original was {:?})",
                current,
                tcx.def_kind(current),
                function
            );
            break None;
        }
    }.unwrap();


    let def_path = tcx.def_path(module);
    let mut crate_name = tcx.original_crate_name(def_path.krate).to_ident_string();
    if crate_name == "main" {
        crate_name = String::new();
    } else {
        crate_name += "::";
    }
    Module(crate_name + &def_path.data.iter().map(|m| format!("{}", m)).join("::"))
}

#[derive(Clone)]
struct CallSite<'tcx> {
    return_variable: Option<mir::Local>,
    function: mir::Operand<'tcx>,
    arguments: Vec<mir::Operand<'tcx>>,
}

fn extract_function_call<'tcx>(tcx: ty::TyCtxt<'tcx>, mir: &mir::Body<'tcx>) -> Vec<CallSite<'tcx>> {
    use mir::visit::Visitor;

    #[derive(Clone)]
    struct SearchFunctionCall<'tcx, 'local> {
        tcx: ty::TyCtxt<'tcx>,
        caller: &'local mir::Body<'tcx>,
        callees: Vec<CallSite<'tcx>>,
    }

    impl<'tcx, 'local> SearchFunctionCall<'tcx, 'local> {
        fn new(tcx: ty::TyCtxt<'tcx>, caller: &'local mir::Body<'tcx>) -> Self {
            SearchFunctionCall{
                tcx,
                caller,
                callees: default()
            }
        }
    }

    impl<'tcx, 'local> Visitor<'tcx> for SearchFunctionCall<'tcx, 'local> {
        fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: mir::Location) {
            if let TerminatorKind::Call{func, args, destination, ..} = &terminator.kind {
                use ty::TyKind::*;
                let callee_fct = func
                    .constant()
                    .map(|cst| match *cst.literal.ty.kind() {
                        FnDef(def_id, _) => Some(self.tcx.def_path_str(def_id)),
                        _ => None,
                    })
                    .flatten();
                dbg!(callee_fct);
                dbg!(&args.first().map(|arg| arg.ty(self.caller, self.tcx)));
                eprintln!();

                self.callees.push(CallSite{
                    return_variable: destination.map(|(place, _)| place.local),
                    function: func.clone(),
                    arguments: args.to_vec(),
                });
            }
        }
    }

    let mut search_callees = SearchFunctionCall::new(tcx, &mir);
    search_callees.visit_body(&mir);
    search_callees.callees
}

/// Intraprocedural analysis that extract the relation between the arguments and the return value of
/// both the function and all called functions.
pub fn extract_dependencies(tcx: ty::TyCtxt<'_>) {
    // let mut monomorphized_functions: HashSet<(DefId, String)> = default();
    let dependencies: HashMap<DefId, FunctionDependencies> = tcx
        .body_owners()
        .map(|caller| {
            eprintln!();
            dbg!(tcx.def_path_str(caller.to_def_id()));
            let mir = tcx.mir_built(ty::WithOptConstParam {
                did: caller,
                const_param_did: tcx.opt_const_param_of(caller)
            });
            let mir = mir.steal();

            let callsites: Vec<CallSite> = extract_function_call(tcx, &mir);

            // Note: arguments[0] == return type, then it's the arguments of the function
            let arguments_name_and_type: IndexVec<mir::Local, (Option<Symbol>, ty::Ty)> = (0..=mir.arg_count)
                .map(mir::Local::from_usize)
                .map(|arg| {
                    let name = mir.var_debug_info
                        .iter()
                        .find(|debug| debug.place.local == arg)
                        .map(|debug| debug.name);
                    let ty = mir.local_decls[arg].ty;
                    (name, ty)
                })
                .collect();

            let deps = direct_dependencies(&mir);
            let deps = propagate_dependencies(deps);
            let Dependencies {
                dependencies,
                constants,
                locals_count,
            } = deps;

            let mut is_return_variable = BitVec::from_elem(locals_count + constants.len(), false);
            for callsite in &callsites {
                if let Some(ret) = callsite.return_variable {
                    is_return_variable.set(ret.as_usize(), true);
                }
            }

            // The source of all locals, are:
            //  - the arguments to the current function
            //  - constants
            //  - the return value of called functions
            let is_argument = |idx: usize| idx < mir.arg_count + 1;
            let is_constant = |idx: usize| idx > locals_count;
            let is_return_variable = |idx: usize| is_return_variable[idx];

            // fn is_callable(ty: ty::Ty) -> bool {
            //     ty.is_fn() || ty.is_fn_ptr() || ty.is_closure()
            // }

            let get_callee_id = |id: usize| {
                callsites
                    .iter()
                    .position(|callsite| callsite.return_variable == Some(mir::Local::from_usize(id)))
                    .unwrap()
            };

            let callees = callsites
                .iter()
                .map(|callsite| {
                    Callee {
                        name: callsite.function.clone(),
                        arguments_source: callsite.arguments
                            // merge the dependencies of all arguments
                            .iter()
                            .map(|arg| {
                                use mir::Operand::*;
                                match arg {
                                    Copy(place) | Move(place) => dependencies[place.local].clone(),
                                    Constant(cst) => {
                                        let mut bitmask = BitVec::from_elem(locals_count + constants.len(), false);
                                        bitmask.set(constants.iter().position(|cst_| cst_ == cst.literal).unwrap(), true);
                                        bitmask
                                    },
                                }
                            })
                            .fold(BitVec::from_elem(locals_count + constants.len(), false), |mut all_dependency, dependency_of_arg| {
                                all_dependency.or(&dependency_of_arg);
                                all_dependency
                            })
                            // search their respective source
                            .iter()
                            .enumerate()
                            .filter_map(|(id, has_dependency)| {
                                has_dependency.then_some(id)
                            })
                            .filter_map(|id| {
                                if is_argument(id) {
                                    Some(Origin::FromArgument(mir::Local::from_usize(id)))
                                } else if is_constant(id) {
                                    Some(Origin::Literal(constants[id - locals_count].clone()))
                                } else if is_return_variable(id) {
                                    Some(Origin::FromReturn(mir::Local::from_usize(get_callee_id(id))))
                                } else {
                                    // Ignore dependencies to local variables
                                    None
                                }
                            })
                            .collect(),
                    }
                })
                .collect();

            (caller.to_def_id(), FunctionDependencies {
                arguments_name_and_type,
                callees,
            })
        })
        .collect();

//  /////////////////////////////
//
//      let mut subfunctions = SearchFunctionCall::new(&depends_from_args);
//      subfunctions.visit_body(mir);
//
//      let caller = caller.to_def_id();
//      functions.insert(caller);
//
//      for (subfunction, depends_from_caller) in subfunctions.inner_functions {
//          // TODO: take a look at
//          // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.upstream_monomorphizations_for
//          let callee_id = if let rustc_middle::ty::FnDef(def_id, _) = subfunction.constant().unwrap().literal.ty.kind() {
//              *def_id
//          } else {
//              unreachable!();
//          };
//          functions.insert(callee_id);
//
//          let callee_str = tcx.def_path_str(callee_id);
//          let full_name = format!("{:?}", subfunction);
//          let monomorphized_call = full_name != callee_str;
//          if monomorphized_call {
//              monomorphized_functions.insert((callee_id, full_name.clone()));
//              dependencies.push((caller, Function::Monomorphized(callee_id, full_name, depends_from_caller)));
//          } else {
//              dependencies.push((caller, Function::Direct(callee_id, depends_from_caller)));
//          }
//      }
//  }
//
//  // Group item by module
//  // TODO: create a hierarchy of module
//  let modules: HashSet<_> = functions
//      .iter()
//      .map(|&f| get_module(tcx, f))
//      .collect();
//  let modules: HashMap<String, usize> = modules
//      .into_iter()
//      .enumerate()
//      .map(|(id, name)| (name, id))
//      .collect();
//
//  let functions = {
//      let mut _functions: HashMap<String, Vec<DefId>> = modules
//          .iter()
//          .map(|(name, _)| (name.clone(), Vec::new()))
//          .collect();
//      for function in functions {
//          _functions.get_mut(&get_module(tcx, function)).unwrap().push(function);
//      }
//      for &(id, _) in &monomorphized_functions {
//          _functions.get_mut(&get_module(tcx, id)).unwrap().push(id);
//      }
//      _functions
//  };
//
//  let monomorphized_functions = {
//      let mut _functions: HashMap<String, Vec<String>> = modules
//          .iter()
//          .map(|(name, _)| (name.clone(), Vec::new()))
//          .collect();
//      for (id, full_name) in monomorphized_functions {
//          _functions.get_mut(&get_module(tcx, id)).unwrap().push(full_name);
//      }
//      _functions
//  };
//
//  /////////////////////////////

    let functions: HashMap<Module, HashSet<DefId>> = {
        let mut functions: HashMap<Module, HashSet<DefId>> = default();
        for (&function, _) in &dependencies {
            let module = get_module(tcx, function);
            functions.entry(module).or_default().insert(function);
        }
        functions
    };

    // FIXME: this doesn't work
    let monomorphized_functions: HashSet<DefId> = dependencies
        .iter()
        .map(|(_, FunctionDependencies{callees, ..})| callees.iter())
        .flatten()
        .map(|callee| &callee.name)
        .filter_map(|callee: &mir::Operand| {
            let generic_name = format!("{:?}", callee);
            callee
                .constant()
                .map(|cst| cst.check_static_ptr(tcx))
                .flatten()
                .map(|def_id| (tcx.def_path_str(def_id) != generic_name).then_some(def_id))
                .flatten()
        })
        .collect();

    // Group item by module
    // TODO: create a hierarchy of module
    let modules: HashSet<&Module> = functions
        .keys()
        .collect();
    let modules: HashMap<&Module, usize> = modules
        .into_iter()
        .enumerate()
        .map(|(module_id, module)| (module, module_id))
        .collect();

    eprintln!("strict digraph {{");

    for (module_name, module_id) in &modules {
        eprintln!("    subgraph cluster{} {{", module_id);
        if module_name.is_empty() {
            // it's the root of the crate
            // for crate_num is &tcx.crates() {
            //     let crate_name = tcx.crate_name(crate_num).to_ident_string();
            // }
            let crate_name = "crate_name"; // FIXME
            eprintln!("        label = <<u>{}</u>>", crate_name);
            eprintln!("        color = none");
        } else {
            // it's a normal module
            eprintln!("        label = <<u>{}</u>>", module_name);
            eprintln!("        color = green");
        }
        eprintln!("        fontcolor = green");
        eprintln!();

        // create function nodes
        for &function in &functions[module_name] {
            let name = tcx.def_path_str(function);
            if monomorphized_functions.contains(&function) {
                // create virtual nodes for monomorphized call");
                eprintln!("        \"{}\" [label=\"\"; fixedsize=\"false\"; width=0; height=0; shape=none]", name);
            } else {
                eprintln!("        \"{}\" [shape=none]", name);
            }
        }


        eprintln!("    }}");
    }

// let dependencies: HashMap<DefId, FunctionDependencies>
//
// /// Store all the dependencies between one function and its callee
// #[derive(Debug, Clone)]
// pub struct FunctionDependencies<'tcx> {
//     /// name and type of the returned value and all the arguments to this function
//     arguments_name_and_type: IndexVec<mir::Local, (Option<Symbol>, ty::Ty<'tcx>)>,
//     /// List of all call-sites inside the body of this function
//     callees: IndexVec<LocalCallee, Callee<'tcx>>,
// }
// 
// /// Store the name of a called function and the source of all of its arguments
// #[derive(Debug, Clone)]
// pub struct Callee<'tcx> {
//     /// name of the called function
//     name: mir::Operand<'tcx>, // FIXME: it should be Constant

//     /// this called function
//     arguments_source: Vec<Origin<'tcx>>,
// }
// 
// /// Express one of the possible source of a given argument
// #[derive(Debug, Clone, Eq, PartialEq, Hash)]
// pub enum Origin<'tcx> {
//     /// A literal expression
//     Literal(ty::Const<'tcx>), // FIXME: it should probably be Const
//     /// An argument of the function being analyzed
//     FromArgument(mir::Local),
//     /// The return value of a another callee
//     FromReturn(mir::Local),
// }


    eprintln!("\n    // dependency graph");
    for (caller, info) in dependencies {
        let caller = tcx.def_path_str(caller);
        for callee in &info.callees {
            if let Some(ty::TyKind::FnDef(def_id, _)) = callee
                .name
                .constant()
                .map(|cst| cst.literal.ty.kind())
            {
                let def_id = *def_id;
                let callee_name = tcx.def_path_str(def_id);

                use def::DefKind::*;
                match tcx.def_kind(def_id) {
                    Fn => {
                        eprintln!("    \"{}\" -> \"{}\"", caller, callee_name);
                    }
                    AssocFn => {
                        eprintln!("    \"{}\" -> \"{}\" // indirect call", caller, callee_name);
                    },
                    other => {
                        eprintln!("    // {} -> {} // ??? {:?}", caller, callee_name, other);
                    }
                }
            } else {
                eprintln!("    // {} -> {:?}", caller, callee.name);
            }


            // match callee {
            //     Function::Direct(callee_id, depends_from_caller) => {
            //         let callee_str = tcx.def_path_str(callee_id);
            //         eprintln!("    \"{}\" -> \"{}\"", caller, callee_str);
            //         if depends_from_caller {
            //             eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", callee_str, caller);
            //         }
            //     },
            //     Function::Monomorphized(callee_id, full_name, depends_from_caller) => {
            //         let caller = tcx.def_path_str(caller);
            //         let callee_str = tcx.def_path_str(callee_id);
            //         eprintln!("    \"{}\" -> \"{}\" [arrowhead=none]", caller, full_name);
            //         eprintln!("    \"{}\" -> \"{}\"", full_name, callee_str);
            //         if depends_from_caller {
            //             eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", callee_str, full_name);
            //             eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", full_name, caller);
            //         }
            //     }
            // }
        }
    }

    eprintln!("}}");
}
