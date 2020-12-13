use bit_vec::BitVec;
use rustc_hir::def;
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir::terminator::*;
use rustc_middle::mir;
use rustc_middle::ty;
use rustc_span::symbol::Symbol;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::collections::HashSet;
use std::default::default;
use std::fmt;

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
    function: DefId,
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
            self.constants.insert(*constant.literal);
        }
    }

    let mut search_constants = Constants::default();
    search_constants.visit_body(mir);

    search_constants.constants
}

#[derive(Debug, Clone)]
/// Describes the dependencies of every variables
///
/// Let start with an example:
///
/// ```no_run
/// fn foo(arg1: i32, arg2: i32) -> i32 {
///     let local = arg;
///     println!("{}", arg2);
///     local * 18;
/// }
/// ```
///
/// In this function, the return value has a direct dependency to `local`, since its value is
/// computed from `local`. It also has a direct dependency to the constant `18`. `local` itself has
/// a direct dependency to `arg1`. Therefore the return value has an indirect dependency to `arg1`,
/// and the constant `18` but no dependency to `arg2`.
///
/// ---
///
/// If `dependency[local][index] == true`, then `local` has a dependency to `index`.
///
/// The index 0 is the return value. Then you have the arguments¹, and all other locals.
/// The index from `locals_count` to then end of the `BitVec` are index into `constants`.
/// For example, if `dependency[local][18] == true` and `locals_count == 15`, this means that
/// `local` has a dependency to the 3rd (`18 - 15`) constants. For conveniency, you can use
/// `self.constant(index)` to get the constant associated with `index`.
///
/// As you have guessed, each `BitVec` in `dependencies` have `constants + locals_count.len()`
/// booleans in them. And `dependencies.len() == locals_count`².
///
/// ¹ The number of arguments can be accessed with `mir.arg_count`. Maybe this should be copied
/// in this struct.
///
/// ² It may not be needed to store `locals_count` in this struct, since `dependencies.len()` is
/// guaranted by construction to be equals to `locals_count`.
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

/// Compute the direct dependency between local variables and constants.
///
/// - see [Dependencies] for more explanations.
/// - dependencies are propagated with [propagate_dependencies].
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

/// Propagates the dependency information computed by [direct_dependencies].
///
/// The input in direct dependencies, and the output are direct + indirect dependencies.
///
/// See [Dependencies] for more information.
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

/// Target of a function call
#[derive(Clone, Debug)]
enum LocalCallType {
    DirectCall(DefId),
    LocalFunctionPtr(mir::Local),
}

#[derive(Clone, Debug)]
struct CallSite<'tcx> {
    // Target of the function call
    function: LocalCallType,
    // Local variable where the return variable is store (if the type isn’t `()`)
    return_variable: Option<mir::Local>,
    // Source of each arguments passed to the function
    arguments: Vec<mir::Operand<'tcx>>,
}

// Extract information about all function call done in `mir`, where `mir` is the body of a function
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
                                other => {
                                    panic!("internal error: unknow call type: {:?}", other);
                                }
                            }
                        } else {
                            panic!("internal error: unknow call type: {:?}", cst);
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

/// Extract the information about the arguments of the function `mir`
fn extract_arguments<'tcx>(mir: &mir::Body<'tcx>) -> Vec<SymbolAndType<'tcx>> {
    mir.args_iter()
        .map(|arg| {
            let symbol = mir
                .var_debug_info
                .iter()
                .find(|debug| {
                    use mir::VarDebugInfoContents::*;
                    match debug.value {
                        Place(place) => place.local == arg,
                        Const(_) => false, // FIXME: should I track constant?
                    }
                })
                .map(|debug| debug.name);
            let ty = mir.local_decls[arg].ty;
            SymbolAndType{symbol, ty}
        })
        .collect()
}

/// Test if a type is the type of a callable object
fn is_callable(ty: &ty::TyS) -> bool {
    ty.is_fn() || ty.is_fn_ptr() || ty.is_closure()
}

/// Intraprocedural analysis that extract the relation between the arguments and the return value of
/// both the function and all called functions.
pub fn extract_dependencies<'tcx>(tcx: ty::TyCtxt<'tcx>) -> AllDependencies<'tcx>
{
    let mut all_dependencies: HashMap<DefId, Function<'_>> = HashMap::new();

    for function in tcx.body_owners() {
        let kind = tcx.def_kind(function);
        if kind != def::DefKind::Fn && kind != def::DefKind::Closure {
            continue;
        }

        let mir = tcx.mir_built(ty::WithOptConstParam {
            did: function,
            const_param_did: tcx.opt_const_param_of(function)
        });
        let mir = mir.borrow();
        let mir: &mir::Body = &mir;

        let caller = function.to_def_id();

        let return_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
        let arguments = extract_arguments(&mir);

        let deps = direct_dependencies(&mir);
        let deps = propagate_dependencies(deps);

        let callsites: Vec<CallSite<'_>> = extract_function_call(tcx, &mir);

        // The source of all locals, are:
        //  - the arguments to the current function
        //  - constants
        //  - the return value of called functions
        let get_origins = |from: mir::Local| /* -> impl Iterator<Item=Source> */ {
            deps.dependencies[from]
                .iter()
                .enumerate()
                .filter_map(|(local, depends_from)| depends_from.then_some(local))
                .filter_map(|local| {
                    if local == 0 {
                        // it's a recursive function
                        Some(Source::ReturnVariable(caller))
                    } else if local <= mir.arg_count {
                        Some(Source::Argument(mir::Local::from_usize(local)))
                    } else if local < deps.locals_count {
                         // note: dependencies to local variable are ignored
                         let local = mir::Local::from_usize(local);
                         callsites
                             .iter()
                             .find(|callsite| callsite.return_variable == Some(local))
                             .map(|callsite| {
                                 if let LocalCallType::DirectCall(callee) = callsite.function {
                                     Some(Source::ReturnVariable(callee))
                                 } else {
                                     // ignore local function pointer
                                     // their dependencies are already propagated
                                     None
                                 }
                             })
                             .flatten()
                    } else {
                        let cst = deps.constants[local - deps.locals_count];
                        if is_callable(cst.ty) {
                            Some(Source::FunctionId(cst))
                        } else {
                            None
                        }
                    }
                })
        };

        let return_deps = get_origins(mir::Local::from_usize(0))
            .map(|source| ReturnDependency { source })
            .collect();

        let mut dependencies = Vec::new();
        for callsite in &callsites {
            use LocalCallType::*;
            match callsite.function {
                DirectCall(callee) => {
                    let mut sources: Vec<Source<'_>> = Vec::new();
                    for arg in &callsite.arguments {
                        use mir::Operand::*;
                        match arg {
                            Copy(place) | Move(place) => {
                                for source in get_origins(place.local) {
                                    sources.push(source);
                                }
                            },
                            Constant(cst) => {
                                if is_callable(cst.literal.ty) {
                                    sources.push(Source::FunctionId(*cst.literal));
                                }
                            }
                        }
                    }

                    dependencies.push(CallerDependency {
                        sources,
                        callee,
                    });
                },
                LocalFunctionPtr(local) => {
                    let _ = local;
                    // TODO
                },
            }
        }

        if let Entry::Vacant(entry) = all_dependencies.entry(caller) {
            entry.insert(Function {
                return_ty,
                arguments,
                dependencies,
                return_deps,
            });
        } else {
            panic!("internal error: the same function is visited multiple times");
        }
    }

    // let internal_functions: HashSet<DefId> = all_dependencies
    //     .keys()
    //     .collect();
    // let external_functions: HashSet<DefId> = all_dependencies
    //     .values()
    //     .map(|function| {
    //         function
    //             .dependencies
    //             .iter()
    //             .map(|CallerDependency{callee, ..}| callee )
    //     })
    //     .flatten()
    //     .collect();
    // let external_functions = all_dependencies
    //     .difference(&internal_functions);

    AllDependencies { functions: all_dependencies }
}

pub struct SymbolAndType<'tcx> {
    symbol: Option<Symbol>,
    ty: ty::Ty<'tcx>,
}

pub enum Source<'tcx> {
    // Note: we could also track special constants, other than functions
    /// when taking a reference to another function
    FunctionId(ty::Const<'tcx>),

    /// argument of the caller
    Argument(mir::Local),

    /// return variable of another callee
    ReturnVariable(DefId),
}

pub struct CallerDependency<'tcx> {
    // Aggregated list of indirect dependencies of all the parameters of this callee
    sources: Vec<Source<'tcx>>,
    // function being called
    callee: DefId,
}

struct ReturnDependency<'tcx> {
    source: Source<'tcx>,
}

pub struct Function<'tcx> { // subgraph (crate local + external functions)
    return_ty: ty::Ty<'tcx>,
    arguments: Vec<SymbolAndType<'tcx>>,
    dependencies: Vec<CallerDependency<'tcx>>, // small blue arrows to a grey circle
    return_deps: Vec<ReturnDependency<'tcx>>, // small blue arrows to the return value
}

pub struct AllDependencies<'tcx> {
    // crate_name: rustc_middle::DefId, // or maybe a Symbol
    // NOTE: Do not forget to add externally defined functions

    /// Informations about functions and closures defined in the current crate
    functions: HashMap<DefId, Function<'tcx>>, // calleer -> callsite
}

/// create and html-escaped string reprensentation for a given symbol
fn print_symbol(symbol: &Option<Symbol>) -> String {
    symbol.map(|s| html_escape::encode_text(&s.to_ident_string()).to_string()).unwrap_or_else(|| String::from("_"))
}

/// Write into `output` a testual reprensentation of `all_dependencies` in dot format
pub fn render_dependencies<'tcx, W: std::io::Write>(
    tcx: ty::TyCtxt<'tcx>,
    all_dependencies: AllDependencies<'tcx>,
    output: &mut W)
-> std::io::Result<()>
{
    //let crate_name = tcx.def_path_str(all_dependencies.crate_name);
    // writeln!(output, "digraph {} {{", crate_name)?;
    writeln!(output, "digraph {{")?;

    writeln!(output, "    subgraph {{")?;
    writeln!(output, "    node [ style=\"filled,solid\" width=10 height=1 color=black fillcolor=lightgrey ]")?;
    writeln!(output)?;

    let mut internal_functions = HashSet::new();

    for (caller, function) in &all_dependencies.functions
    {
        internal_functions.insert(caller);

        let caller_name = tcx.def_path_str(*caller);
        let escaped_caller_name = html_escape::encode_text(&caller_name);

        // TODO: add grouping by module? Maybe using a different color

        writeln!(output, "    \"{}\" [ label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\"><tr>", caller_name)?;
        writeln!(output, "        <td port=\"function\"><font color='red'>{}</font></td>", escaped_caller_name)?;
        // writeln!(output, "            <td>&lt;</td>")?;
        // writeln!(output, "            <td><font color='darkgreen'>Fct</font>: Fn()</td>")?;
        // writeln!(output, "            <td>&gt;</td>")?;
        writeln!(output, "        <td>(</td>")?;
        for (arg_id, SymbolAndType{symbol, ty}) in function.arguments.iter().enumerate() {
            let arg_id = arg_id + 1; // 0 is the return variable
            let symbol = print_symbol(symbol);
            let ty: ty::subst::GenericArg<'_> = (*ty).into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            writeln!(output, "            <td port=\"{}\">{}: <font color='darkgreen'>{}</font></td>", arg_id, symbol, ty)?;
        }
        writeln!(output, "        <td>)</td>")?;
        if !function.return_ty.is_unit() {
            let ty: ty::subst::GenericArg<'_> = function.return_ty.into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            let right_arrow = "&#8594;";
            writeln!(output, "        <td> {} </td>", right_arrow)?;
            writeln!(output, "        <td port=\"0\"><font color='darkgreen'>{}</font></td>", ty)?;
        }
        writeln!(output, "        </tr></table>>")?;
        writeln!(output, "    ]")?;
    }
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(output, "    node [ style=\"filled,dotted\" width=10 height=1 color=black fillcolor=white ]")?;
    writeln!(output)?;

    let mut indirect_dependencies = HashSet::new();
    for (caller, function) in all_dependencies.functions.iter() {
        let caller_name = tcx.def_path_str(*caller);
        let mut callees = HashSet::new();
        for CallerDependency{sources, callee} in function.dependencies.iter() {
            let callee_name = tcx.def_path_str(*callee);
            for source in sources {
                use Source::*;
                match source {
                    FunctionId(source) => {
                        // FIXME
                        let source_name = tcx.mk_const(*source);

                        // WTF: it seems that source_name can be printed as "\"crate-name\""?
                        // ```
                        // ""crate-name"":function -> "opts to stable"  [ color=blue arrowtail=empty ]
                        // ```
                        if !indirect_dependencies.contains(&(source, caller)) {
                            indirect_dependencies.insert((source, caller));
                            writeln!(output, "    \"{}\":function -> \"{}\"  [ color=blue arrowtail=empty ]", source_name, caller_name)?;
                        }
                    },
                    Argument(_arg) => {
                        // dependencies between args add to much noice

                        // writeln!(output, "    \"{}\":{} -> \"{}\"  [ color=blue arrowtail=empty ]", caller_name, arg.as_usize(), callee_name)?;
                    },
                    ReturnVariable(_previous_callee) => {
                        // dependencies between return type add to much noice

                        // let previous_callee_name = tcx.def_path_str(*previous_callee);
                        // writeln!(output, "    \"{} to {}\" -> \"{} to {}\"  [ color=blue arrowtail=empty ]", caller_name, previous_callee_name, caller_name, callee_name)?;
                    },
                }
            }

            // create only one arrow even if the same function is called multiple times
            if !callees.contains(callee) {
                callees.insert(callee);

                let style = if internal_functions.contains(callee) {
                    "solid"
                } else {
                    "dotted"
                };

                if caller == callee {
                    writeln!(output, "    \"{}\":0 -> \"{}\" [ color=black arrowhead=empty style={} ]", caller_name, caller_name, style)?;
                } else {
                    writeln!(output, "    \"{}\" -> \"{}\" [ color=black arrowhead=empty style={} ]", caller_name, callee_name, style)?;
                }
            }
        }
        for ReturnDependency{source} in function.return_deps.iter() {
            use Source::*;
            match source {
                FunctionId(source) => {
                    let source_name = tcx.mk_const(*source);

                    // WTF: it seems that source_name can be printed as "\"crate-name\""?
                    // ```
                    // ""crate-name"":function -> "opts to stable"  [ color=blue arrowtail=empty ]
                    // ```
                    writeln!(output, "    \"{}\":function -> \"{}\":0  [ color=blue arrowtail=empty ]", source_name, caller_name)?;
                },
                Argument(_arg) => {
                    // dependencies from arguments add to much noice

                    // writeln!(output, "    \"{}\":{} -> \"{}\":0  [ color=blue arrowtail=empty ]", caller_name, arg.as_usize(), caller_name)?;
                },
                ReturnVariable(_previous_callee) => {
                    // dependencies from other return type add to much noice

                    // if caller != previous_callee {
                    //     let previous_callee_name = tcx.def_path_str(*previous_callee);
                    //     writeln!(output, "    \"{} to {}\" -> \"{}\":0  [ color=blue arrowtail=empty ]", caller_name, previous_callee_name, caller_name)?;
                    // }
                },
            }
        }
    }

    writeln!(output, "}}")?;

    Ok(())
}
