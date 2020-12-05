use bit_vec::BitVec;
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

#[derive(Clone, Debug)]
enum CallType<'tcx> {
    DirectCall(DefId),
    // IndirectCall(DefId, Vec<Origin<'tcx>>),
    FromLocalPointer(Vec<Origin<'tcx>>),
}

/// Store the name of a called function and the source of all of its arguments
#[derive(Debug, Clone)]
pub struct Callee<'tcx> {
    /// name of the called function
    function: CallType<'tcx>,
    /// source (possibly over-approximated) of the source of the arguments to
    /// this called function
    arguments_source: Vec<Origin<'tcx>>,
}

/// Express one of the possible source of a given argument
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Origin<'tcx> {
    /// A literal expression
    Literal(ty::Const<'tcx>),
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

impl<'tcx> Dependencies<'tcx> {
    fn constant(&self, idx: usize) -> ty::Const<'tcx> {
        assert!(idx >= self.locals_count);
        self.constants[idx - self.locals_count]
    }
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
    let constants: Vec<ty::Const<'_>> = extract_constant(mir).into_iter().collect();
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

// impl Module {
//     pub fn is_empty(&self) -> bool {
//         self.0.is_empty()
//     }
// }

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// /// Return the name of the module of a given function
// fn get_module(tcx: ty::TyCtxt<'_>, function: DefId) -> Module {
//     use ty::DefIdTree;
// 
//     let mut current = function;
//     // The immediate parent might not always be a module.
//     // Find the first parent which is.
//     let module = loop {
//         if let Some(parent) = tcx.parent(current) {
//             if tcx.def_kind(parent) == rustc_hir::def::DefKind::Mod {
//                 break Some(parent);
//             }
//             current = parent;
//         } else {
//             debug!(
//                 "{:?} has no parent (kind={:?}, original was {:?})",
//                 current,
//                 tcx.def_kind(current),
//                 function
//             );
//             break None;
//         }
//     }.unwrap();
// 
// 
//     let def_path = tcx.def_path(module);
//     let mut crate_name = tcx.original_crate_name(def_path.krate).to_ident_string();
//     if crate_name == "main" {
//         crate_name = String::new();
//     } else {
//         crate_name += "::";
//     }
//     Module(crate_name + &def_path.data.iter().map(|m| format!("{}", m)).join("::"))
// }

#[derive(Clone, Debug)]
enum LocalCallType {
    DirectCall(DefId),
    // IndirectCall(DefId, mir::Local),
    LocalFunctionPtr(mir::Local),
}

#[derive(Clone, Debug)]
struct CallSite<'tcx> {
    return_variable: Option<mir::Local>,
    function: LocalCallType,
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
                use mir::Operand::*;
                let function = match func {
                    Constant(cst) => {
                        if let ty::TyKind::FnDef(def_id, _) = cst.literal.ty.kind() {
                            let def_id = *def_id;

                            use def::DefKind::*;
                            match self.tcx.def_kind(def_id) {
                                Fn | AssocFn => LocalCallType::DirectCall(def_id),
                                // AssocFn => match &args[0] {
                                //     Move(place) | Copy(place) => LocalCallType::IndirectCall(def_id, place.local),
                                //     Constant(cst) => {
                                //         if let ty::TyKind::FnDef(def_id, _) = cst.literal.ty.kind() {
                                //             LocalCallType::DirectCall(*def_id)
                                //         } else {
                                //             panic!()
                                //         }
                                //     },
                                // },
                                other => {
                                    panic!("unknow call type: {:?}", other);
                                }
                            }
                        } else {
                            panic!("unknow call type: {:?}", cst);
                        }
                    },
                    Move(place) | Copy(place) => LocalCallType::LocalFunctionPtr(place.local),
                };

                self.callees.push(CallSite{
                    return_variable: destination.map(|(place, _)| place.local),
                    function,
                    arguments: args.to_vec(),
                });
            }
        }
    }

    let mut search_callees = SearchFunctionCall::new(tcx, &mir);
    search_callees.visit_body(&mir);
    search_callees.callees
}

// fn get_generic_name(tcx: ty::TyCtxt<'_>, def_id: DefId) -> String {
//     match tcx.opt_associated_item(def_id) {
//         Some(ty::AssocItem{def_id, ..}) => {
//             tcx.def_path_str(*def_id)
//         },
//         None => tcx.def_path_str(def_id),
//     }
// }

fn extract_arguments(mir: &'tcx mir::Body) -> Vec<SymbolAndType<'tcx>> {
    mir.args_iter()
        .map(|arg| {
            let symbol = mir
                .var_debug_info
                .iter()
                .find(|debug| debug.place.local == arg)
                .map(|debug| debug.name);
            let ty = mir.local_decls[arg].ty;
            SymbolAndType{symbol, ty}
        })
        .collect()
}

/// Intraprocedural analysis that extract the relation between the arguments and the return value of
/// both the function and all called functions.
pub fn extract_and_render_dependencies<'tcx, W: std::io::Write>(tcx: ty::TyCtxt<'tcx>, output: &mut W) -> std::io::Result<()>
{
    // EXTRACT

    let functions: Vec<_> = tcx
        .body_owners()
        .map(|function| {
            let mir = tcx.mir_built(ty::WithOptConstParam {
                did: function,
                const_param_did: tcx.opt_const_param_of(function)
            });
            (mir.borrow(), function.to_def_id())
        })
        .collect();
    let functions: Vec<(&'_ mir::Body, DefId)> = functions
        .iter()
        .map(|(mir, caller)| {
            let mir: &mir::Body = &mir;
            (mir, *caller)
        })
        .collect();

    let mut all_dependencies: HashMap<DefId, Function<'_>> = HashMap::new();

    for (mir, caller) in functions.iter() {
        let return_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
        let arguments = extract_arguments(&mir);
        let function = all_dependencies.entry(*caller).or_insert_with(|| Function {
            return_ty,
            arguments,
            caller_deps: Vec::new(),
            callee_deps: Vec::new(),
            return_deps: Vec::new(),
        });

        let deps = direct_dependencies(&mir);
        let deps = propagate_dependencies(deps);

        let callsites: Vec<CallSite<'_>> = extract_function_call(tcx, &mir);
        for callsite in &callsites {
            use LocalCallType::*;
            match callsite.function {
                DirectCall(callee) => {
                    let mut sources: Vec<Source<'_>> = Vec::new();
                    for arg in &callsite.arguments {
                        use mir::Operand::*;
                        match arg {
                            Copy(place) | Move(place) => {
                                for (local, depends_from) in deps.dependencies[place.local].iter().enumerate() {
                                     if !depends_from {
                                         continue;
                                     }

                                     if local <= mir.arg_count {
                                         sources.push(Source::Argument(mir::Local::from_usize(local)));
                                     } else if local < deps.locals_count { // FIXME: off by 1 error ?
                                         // note: dependencies to local variable are ignored
                                         let local = mir::Local::from_usize(local);
                                         for callsite in &callsites {
                                             if callsite.return_variable == Some(local) {
                                                 if let DirectCall(callee) = callsite.function {
                                                     sources.push(Source::ReturnVariable(callee));
                                                     break;
                                                 } else {
                                                     panic!();
                                                 }
                                             }
                                         }
                                     } else {
                                         sources.push(Source::FunctionId(deps.constants[local - deps.locals_count]));
                                     }
                                }
                            },
                            Constant(cst) => {
                                sources.push(Source::FunctionId(*cst.literal));
                            }
                        }
                    }

                    function.caller_deps.push(CallerDependency {
                        sources,
                        callee,
                    });
                },
                LocalFunctionPtr(local) => {
                    let _ =local;
                    // TODO
                },
            }
        }


        /*
        struct XXX<'mir, 'deps, 'tcx> {
            mir: &'mir mir::Body<'tcx>,
            deps: &'deps Dependencies<'tcx>,
            // callsites: &'callsites Vec<CallSite<'tcx>>,
            is_return_variable: BitVec,
        }
        impl<'mir, 'deps, 'tcx> XXX<'mir, 'deps, 'tcx> {
            pub fn new(mir: &'mir mir::Body<'tcx>, deps: &'deps Dependencies<'tcx>, callsites: &Vec<CallSite<'tcx>>) -> Self {
                let mut is_return_variable = BitVec::from_elem(deps.locals_count + deps.constants.len(), false);
                is_return_variable.set(0, true);
                for callsite in callsites {
                    if let Some(ret) = callsite.return_variable {
                        is_return_variable.set(ret.as_usize(), true);
                    }
                }

                XXX {
                    mir,
                    deps,
                    // callsites,
                    is_return_variable,
                }
            }

            // The source of all locals, are:
            //  - the arguments to the current function
            //  - constants
            //  - the return value of called functions
            fn is_argument(&self, idx: usize) -> bool {
                // + 1 for the return value of the function
                0 < idx && idx < self.mir.arg_count + 1
            }
            fn is_constant(&self, idx: usize) -> bool {
                idx >= self.deps.locals_count
            }
            fn is_return_variable(&self, idx: usize) -> bool {
                self.is_return_variable[idx]
            }

            // fn is_callable(ty: ty::Ty) -> bool {
            //     ty.is_fn() || ty.is_fn_ptr() || ty.is_closure()
            // }

            // fn get_callee_id(&self, id: usize) -> usize {
            //     self.callsites
            //         .iter()
            //         .position(|callsite| callsite.return_variable == Some(mir::Local::from_usize(id)))
            //         .unwrap()
            // }

            pub fn get_origins(&self, dependencies: &BitVec) -> Vec<Origin<'tcx>> {
                dependencies
                    .iter()
                    .enumerate()
                    .filter(|(_, is_dependency)| *is_dependency)
                    .filter_map(|(id, _)| {
                        if self.is_return_variable(id) {
                            Some(Origin::FromReturn(mir::Local::from_usize(id)))
                        } else if self.is_argument(id) {
                            Some(Origin::FromArgument(mir::Local::from_usize(id)))
                        } else if self.is_constant(id) {
                            Some(Origin::Literal(self.deps.constant(id)))
                        } else {
                            // ignore local variable
                            None
                        }
                    })
                    .collect()
            }

            fn origins_from_local(&self, local: mir::Local) -> Vec<Origin<'tcx>> {
                self.get_origins(&self.deps.dependencies[local])
            }

            pub fn get_source(&self, fct: &LocalCallType) -> CallType<'tcx> {
                use LocalCallType::*;
                match fct {
                    DirectCall(def_id) => CallType::DirectCall(*def_id),
                    // IndirectCall(def_id, local) => CallType::IndirectCall(*def_id, self.origins_from_local(*local)),
                    LocalFunctionPtr(local) => {
                        let origins = self.origins_from_local(*local);
                        if origins.len() == 1 {
                            if let Origin::Literal(cst) = origins[0] {
                                if let ty::TyKind::FnDef(def_id, _) = cst.ty.kind() {
                                    CallType::DirectCall(*def_id)
                                } else {
                                    panic!()
                                }
                            } else {
                                CallType::FromLocalPointer(origins)
                            }
                        } else {
                            CallType::FromLocalPointer(origins)
                        }
                    },
                }
            }
        }

        let xxx = XXX::new(&mir, &deps, &callsites);
        let callees = callsites
            .iter()
            .map(|callsite| {
                Callee {
                    function: xxx.get_source(&callsite.function),
                    arguments_source: {
                        let dependencies = callsite.arguments
                            // merge the dependencies of all arguments
                            .iter()
                            .map(|arg| {
                                use mir::Operand::*;
                                match arg {
                                    Copy(place) | Move(place) => deps.dependencies[place.local].clone(),
                                    Constant(cst) => {
                                        let mut bitmask = BitVec::from_elem(deps.locals_count + deps.constants.len(), false);
                                        bitmask.set(deps.constants.iter().position(|cst_| cst_ == cst.literal).unwrap(), true);
                                        bitmask
                                    },
                                }
                            })
                            .fold(BitVec::from_elem(deps.locals_count + deps.constants.len(), false), |mut all_dependency, dependency_of_arg| {
                                all_dependency.or(&dependency_of_arg);
                                all_dependency
                            });
                        xxx.get_origins(&dependencies)
                    },
                }
            })
            .collect();

        (caller.to_def_id(), FunctionDependencies {
            arguments_name_and_type,
            callees,
        })
        */
    }

    let all_dependencies = AllDependencies { functions: all_dependencies };
    render_dependencies(tcx, all_dependencies, output)
}

pub struct SymbolAndType<'tcx> {
    symbol: Option<Symbol>,
    ty: ty::Ty<'tcx>,
}

pub enum Source<'tcx> {
    FunctionId(ty::Const<'tcx>), // when taking a reference to another function
    Argument(mir::Local), // argument of the caller
    ReturnVariable(DefId), // return variable of another callee
}
pub struct CallerDependency<'tcx> {
    sources: Vec<Source<'tcx>>,
    callee: DefId,
}
pub struct CalleeDependency {
    called_by: DefId,
    targets: Vec<mir::Local>, // argument
}
struct ReturnDependency<'tcx> {
    source: Source<'tcx>,
}

pub struct Function<'tcx> { // subgraph (crate local + external functions)
    return_ty: ty::Ty<'tcx>,
    arguments: Vec<SymbolAndType<'tcx>>,
    caller_deps: Vec<CallerDependency<'tcx>>, // small blue arrows to a grey circle
    callee_deps: Vec<CalleeDependency>, // small blue arrows from a white circle
    return_deps: Vec<ReturnDependency<'tcx>>, // small blue arrows to the return value
}

pub struct AllDependencies<'tcx> {
    // crate_name: rustc_middle::DefId, // or maybe a Symbol
    // NOTE: Do not forget to add externally defined functions
    functions: HashMap<DefId, Function<'tcx>>, // calleer -> callsite
}

fn print_symbol(symbol: &Option<Symbol>) -> String {
    symbol.map(|s| html_escape::encode_text(&s.to_ident_string()).to_string()).unwrap_or_else(|| String::from("_"))
}

pub fn render_dependencies<'tcx, 'dependencies, W: std::io::Write>(
    tcx: ty::TyCtxt<'tcx>,
    all_dependencies: AllDependencies<'dependencies>,
    output: &mut W)
-> std::io::Result<()>
{
    writeln!(output, "digraph {{")?;
    //let crate_name = tcx.def_path_str(all_dependencies.crate_name);
    // writeln!(output, "digraph {} {{", crate_name)?;
    writeln!(output, "    node [ shape=none ]")?;
    writeln!(output)?;
    for (subgraph_id, (caller, function)) in all_dependencies
        .functions
        .iter()
        .enumerate()
        .map(|(id, fct)| (id + 1, fct)) // arguments id starts from 1
    {
        let caller_name = tcx.def_path_str(*caller);
        let escaped_caller_name = html_escape::encode_text(&caller_name);

        // TODO: add grouping by module?

        writeln!(output, "    subgraph cluster_{:03} {{", subgraph_id)?;
        writeln!(output, "        color=grey")?;
        writeln!(output)?;
        writeln!(output, "        \"{}\" [label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\"><tr>", caller_name)?;
        writeln!(output, "            <td port=\"function\"><font color='red'>{}</font></td>", escaped_caller_name)?;
        // writeln!(output, "            <td>&lt;</td>")?;
        // writeln!(output, "            <td><font color='darkgreen'>Fct</font>: Fn()</td>")?;
        // writeln!(output, "            <td>&gt;</td>")?;
        writeln!(output, "            <td>(</td>")?;
        for (arg_id, SymbolAndType{symbol, ty}) in function.arguments.iter().enumerate() {
            let symbol = print_symbol(symbol);
            let ty: ty::subst::GenericArg<'_> = (*ty).into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            writeln!(output, "            <td port=\"{}\">{}: <font color='darkgreen'>{}</font></td>", arg_id, symbol, ty)?;
        }
        writeln!(output, "            <td>)</td>")?;
        if !function.return_ty.is_unit() {
            let ty: ty::subst::GenericArg<'_> = function.return_ty.into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            let right_arrow = "&#8594;";
            writeln!(output, "            <td> {} </td>", right_arrow)?;
            writeln!(output, "            <td port=\"return\"><font color='darkgreen'>{}</font></td>", ty)?;
        }
        writeln!(output, "            </tr></table>>")?;
        writeln!(output, "        ]")?;
        writeln!(output, "        {{")?;
        writeln!(output, "            rank=same")?;
        for CallerDependency{callee, ..} in function.caller_deps.iter() {
            let callee_name = tcx.def_path_str(*callee);
            writeln!(output, "            \"{} to {}\" [ style=filled label=\"\" width=0.2; height=0.2; shape=circle ]", caller_name, callee_name)?;
        }
        for CalleeDependency{called_by, ..} in function.callee_deps.iter() {
            let called_by_name = tcx.def_path_str(*called_by);
            writeln!(output, "            \"{} from {}\" [ label=\"\" width=0.2; height=0.2; shape=circle ]", caller_name, called_by_name)?;
        }
        writeln!(output, "        }}")?;
        writeln!(output, "    }}")?;
    }
    writeln!(output)?;

    for (caller, function) in all_dependencies.functions.iter() {
        let caller_name = tcx.def_path_str(*caller);
        for CallerDependency{sources, callee} in function.caller_deps.iter() {
            let callee_name = tcx.def_path_str(*callee);
            for source in sources {
                use Source::*;
                match source {
                    FunctionId(source) => {
                        let source_name = source;
                        writeln!(output, "    \"{}\":function -> \"{} to {}\"  [ color=\"blue\" arrowtail=empty ]", source_name, caller_name, callee_name)?;
                    },
                    Argument(arg) => {
                        writeln!(output, "    \"{}\":{} -> \"{} to {}\"  [ color=\"blue\" arrowtail=empty ]", caller_name, arg.as_usize(), caller_name, callee_name)?;
                    },
                    ReturnVariable(previous_callee) => {
                        let previous_callee_name = tcx.def_path_str(*previous_callee);
                        writeln!(output, "    \"{} to {}\" -> \"{} to {}\"  [ color=\"blue\" arrowtail=empty ]", caller_name, previous_callee_name, caller_name, callee_name)?;
                    },
                }
            }
            writeln!(output, "    \"{} to {}\" -> \"{} from {}\" [ color=\"black:invis:black\" arrowhead=empty ]", caller_name, callee_name, callee_name, caller_name)?;
        }
        for CalleeDependency{called_by, targets} in function.callee_deps.iter() {
            let called_by_name = tcx.def_path_str(*called_by);
            for target in targets {
                writeln!(output, "    \"{} from {}\" -> \"{}\":{}  [ color=\"blue\" arrowtail=empty ]", caller_name, called_by_name, caller_name, target.as_usize())?;
            }
        }
        for ReturnDependency{source} in function.return_deps.iter() {
            use Source::*;
            match source {
                FunctionId(source) => {
                    let source_name = source;
                    writeln!(output, "    \"{}\":function -> \"{}\":return  [ color=\"blue\" arrowtail=empty ]", source_name, caller_name)?;
                },
                Argument(arg) => {
                    writeln!(output, "    \"{}\":{} -> \"{}\":return  [ color=\"blue\" arrowtail=empty ]", caller_name, arg.as_usize(), caller_name)?;
                },
                ReturnVariable(previous_callee) => {
                    let previous_callee_name = tcx.def_path_str(*previous_callee);
                    writeln!(output, "    \"{} to {}\" -> \"{}\":return  [ color=\"blue\" arrowtail=empty ]", caller_name, previous_callee_name, caller_name)?;
                },
            }
        }
    }

    writeln!(output, "}}")?;

    Ok(())
}
