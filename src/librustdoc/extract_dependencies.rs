#![forbid(dead_code)]

/// Extract relationship between all the locals in a function
use bit_vec::BitVec;
use rustc_hir::def;
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir;
use rustc_middle::mir::terminator::*;
use rustc_middle::ty;
use rustc_span::symbol::Symbol;
use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::collections::HashSet;
use std::default::default;
use std::fmt;

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
/// If `dependency[index][index] == true`, then `index` has a dependency to `index`.
///
/// `dependencies` is a 2D array with `dependencies.len() + constants.len()` columns.
///
/// The column 0 is the return value. Then you have the arguments (from index `1` to `arg_count +
/// 1`), then all other locals up to `dependencies.len()`. The last `constants.len()` indexes of
/// the `BitVec` are indexes into `constants`.
///
/// For example, if `dependency[index][18] == true` and `dependencies.len() == 15`, this means that
/// `index` has a dependency to the 3rd (`18 - 15`) constant. To access it conveniently, you can
/// use `self.constant(index)` to get the constant associated with `index`.
#[derive(Debug, Clone)]
pub struct Dependencies<'tcx> {
    dependencies: IndexVec<mir::Local, BitVec>,
    constants: Vec<ty::Const<'tcx>>,
    arg_count: usize,
}

#[derive(Debug, Clone)]
pub enum DependencyType<'tcx> {
    Return,
    Argument(mir::Local),
    Local(mir::Local),
    Constant(ty::Const<'tcx>),
}

impl<'tcx> Dependencies<'tcx> {
    /// Compute the direct dependency between local variables and constants.
    ///
    /// - see [Dependencies] for more explanations.
    /// - dependencies are propagated with [propagate].
    fn direct_dependencies<'mir>(function: &'mir mir::Body<'tcx>) -> Self {
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
        let locals_count = function.local_decls.len();
        let constants: Vec<ty::Const<'_>> = extract_constant(function).into_iter().collect();
        let mut dependencies = IndexVec::from_elem_n(
            BitVec::from_elem(locals_count + constants.len(), false),
            locals_count,
        );

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
                _: mir::Location,
            ) {
                let lvalue = lvalue.local;

                let constants = self.constants;
                let locals_count = self.locals_count;
                let dependencies: &mut IndexVec<mir::Local, BitVec> = self.dependencies;

                let get_id = |op: &mir::Operand<'tcx>| -> usize {
                    use mir::Operand::*;
                    match op {
                        Copy(place) | Move(place) => place.local.as_usize(),
                        Constant(constant) => {
                            locals_count
                                + constants
                                    .iter()
                                    .position(|cst| cst == constant.literal)
                                    .unwrap()
                        }
                    }
                };

                use mir::Rvalue::*;
                match rvalue {
                    Use(op) | Repeat(op, _) | Cast(_, op, _) | UnaryOp(_, op) => {
                        dependencies[lvalue].set(get_id(op), true);
                    }
                    Ref(_, _, place) | AddressOf(_, place) | Len(place) | Discriminant(place) => {
                        dependencies[lvalue].set(place.local.as_usize(), true);
                    }
                    ThreadLocalRef(_) => {
                        () // TODO:add support to threadlocal
                    }
                    BinaryOp(_, op1, op2) | CheckedBinaryOp(_, op1, op2) => {
                        dependencies[lvalue].set(get_id(op1), true);
                        dependencies[lvalue].set(get_id(op2), true);
                    }
                    NullaryOp(_, _) => {
                        () // no dependencies
                    }
                    Aggregate(_, ops) => {
                        for op in ops {
                            dependencies[lvalue].set(get_id(op), true);
                        }
                    }
                }
            }
        }

        let mut search_constants = Assignments::new(locals_count, &constants, &mut dependencies);
        search_constants.visit_body(function);

        Dependencies {
            dependencies,
            constants,
            arg_count: function.arg_count,
        }
    }

    /// Propagates the dependency information computed by [direct_dependencies].
    ///
    /// The input in direct dependencies, and the output are direct + indirect dependencies.
    ///
    /// See [Dependencies] for more information.
    fn propagate(self) -> Self {
        let Dependencies {
            mut dependencies,
            constants,
            arg_count,
        } = self;

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

        let mut previous_iteration = BitVec::from_elem(dependencies.len() + constants.len(), false);
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
                right.iter().enumerate().map(|(i, x)| (i + 1, x)),
            );

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
        Dependencies {
            dependencies,
            constants,
            arg_count,
        }
    }

    /// Return all the dependencies to `local`
    fn dependencies(&self, local: mir::Local) -> impl Iterator<Item = DependencyType<'tcx>> + '_ {
        self.dependencies[local]
            .iter()
            .enumerate()
            .filter_map(|(index, depends_from)| depends_from.then_some(index))
            .map(move |index| {
                if index == 0 {
                    DependencyType::Return
                } else if index <= self.arg_count {
                    DependencyType::Argument(mir::Local::from_usize(index))
                } else if index < self.dependencies.len() {
                    DependencyType::Local(mir::Local::from_usize(index))
                } else {
                    DependencyType::Constant(self.constants[index - self.dependencies.len()])
                }
            })
    }
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
    /// Target of the function call
    function: LocalCallType,
    /// Local variable where the return variable is store (if the type isn’t `()`)
    return_variable: Option<mir::Local>,
    /// Source of each arguments passed to the function
    arguments: Vec<mir::Operand<'tcx>>,
}

#[derive(Debug, Clone)]
pub struct SymbolAndType<'tcx> {
    symbol: Option<Symbol>,
    ty: ty::Ty<'tcx>,
}

/// Dependencies of a given local
///
/// Note: we could also track special constants, other than functions
#[derive(Debug, Clone)]
pub enum Source<'tcx> {
    /// a reference to another function
    FunctionId(ty::Const<'tcx>),

    /// argument of the caller
    Argument(mir::Local),

    /// return variable of another callee
    ReturnVariable(DefId),
}

#[derive(Debug, Clone)]
pub enum Callee<'tcx> {
    DirectCall(DefId),
    LocalFunctionPtr(Vec<Source<'tcx>>),
}

#[derive(Debug, Clone)]
pub struct CallerDependency<'tcx> {
    /// Aggregated list of indirect dependencies of all the parameters of this callee
    sources: Vec<Source<'tcx>>,
    /// function being called
    callee: Callee<'tcx>,
}

#[derive(Debug, Clone)]
pub struct Function<'tcx> {
    return_ty: ty::Ty<'tcx>,
    arguments: Vec<SymbolAndType<'tcx>>,
    dependencies: Vec<CallerDependency<'tcx>>,
    return_deps: Vec<Source<'tcx>>,
}

#[derive(Debug, Clone)]
pub struct AllDependencies<'tcx> {
    // TODO:
    // crate_name: rustc_middle::DefId, // or maybe a Symbol

    // FIXME: externally defined functions are missing
    /// Informations about functions and closures defined in the current crate
    functions: HashMap<DefId, Function<'tcx>>, // calleer -> callsite
}

/// Extract all constants being used in a given function
fn extract_constant<'tcx>(function: &mir::Body<'tcx>) -> HashSet<ty::Const<'tcx>> {
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
    search_constants.visit_body(function);

    search_constants.constants
}

/// Extract information about all function calls in `function`
fn extract_function_call<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    function: &mir::Body<'tcx>,
) -> Vec<CallSite<'tcx>> {
    use mir::visit::Visitor;

    #[derive(Clone)]
    struct SearchFunctionCall<'tcx, 'local> {
        tcx: ty::TyCtxt<'tcx>,
        caller: &'local mir::Body<'tcx>,
        callees: Vec<CallSite<'tcx>>,
    }

    impl<'tcx, 'local> SearchFunctionCall<'tcx, 'local> {
        fn new(tcx: ty::TyCtxt<'tcx>, caller: &'local mir::Body<'tcx>) -> Self {
            SearchFunctionCall {
                tcx,
                caller,
                callees: default(),
            }
        }
    }

    impl<'tcx, 'local> Visitor<'tcx> for SearchFunctionCall<'tcx, 'local> {
        fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: mir::Location) {
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            {
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
                    }
                    Move(place) | Copy(place) => LocalCallType::LocalFunctionPtr(place.local),
                };

                self.callees.push(CallSite {
                    return_variable: destination.map(|(place, _)| place.local),
                    function,
                    arguments: args.to_vec(),
                });
            }
        }
    }

    let mut search_callees = SearchFunctionCall::new(tcx, &function);
    search_callees.visit_body(&function);
    search_callees.callees
}

/// Extract the information about the arguments of `function`
fn extract_arguments<'tcx>(function: &mir::Body<'tcx>) -> Vec<SymbolAndType<'tcx>> {
    function
        .args_iter()
        .map(|arg| {
            let symbol = function
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
            let ty = function.local_decls[arg].ty;
            SymbolAndType { symbol, ty }
        })
        .collect()
}

/// Test if a type is the type of a callable object
fn is_callable(ty: &ty::TyS) -> bool {
    ty.is_fn() || ty.is_fn_ptr() || ty.is_closure()
}

/// Intraprocedural analysis that extract the relation between the arguments and the return value of
/// both the function and all called functions.
pub fn extract_dependencies<'tcx>(tcx: ty::TyCtxt<'tcx>) -> AllDependencies<'tcx> {
    let mut all_dependencies: HashMap<DefId, Function<'_>> = HashMap::new();

    for function in tcx.body_owners() {
        match tcx.def_kind(function) {
            def::DefKind::Fn
            | def::DefKind::AssocFn
            | def::DefKind::Closure
            | def::DefKind::Generator => (),
            _ => continue,
        }

        let mir = tcx.mir_built(ty::WithOptConstParam {
            did: function,
            const_param_did: tcx.opt_const_param_of(function),
        });
        let mir = mir.borrow();
        let mir: &mir::Body = &mir;

        let caller = function.to_def_id();

        let return_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
        let arguments = extract_arguments(&mir);

        let deps = Dependencies::direct_dependencies(&mir).propagate();

        let callsites: Vec<CallSite<'_>> = extract_function_call(tcx, &mir);

        // The source of all locals, are:
        //  - the arguments to the current function
        //  - constants
        //  - the return value of called functions
        let get_origins = |from: mir::Local| /* -> impl Iterator<Item=Source> */ {
            deps.dependencies(from)
                .filter_map(|dep| {
                    use DependencyType::*;
                    match dep {
                        Return => {
                            // it's a recursive function
                            Some(Source::ReturnVariable(caller))
                        },
                        Argument(arg) => {
                            Some(Source::Argument(arg))
                        },
                        Local(local) => {
                             callsites
                                 .iter()
                                 .find(|callsite| callsite.return_variable == Some(local))
                                 .map(|callsite| {
                                     use LocalCallType::*;
                                     match callsite.function {
                                         DirectCall(callee) => Some(Source::ReturnVariable(callee)),
                                         LocalFunctionPtr(local) => {
                                             if local.as_usize() <= mir.arg_count {
                                                 Some(Source::Argument(local))
                                             } else {
                                                 // FIXME:
                                                 // ignore dependencies of function pointers,
                                                 eprintln!("warning ignoring indirect dependencies in {:?}", caller);
                                                 None
                                             }
                                         }
                                     }
                                 })
                                 .flatten()
                        },
                        Constant(cst) =>
                            if is_callable(cst.ty) {
                                Some(Source::FunctionId(cst))
                            } else {
                                None
                            }
                        }
                })
        };

        let return_deps = get_origins(mir::Local::from_usize(0)).collect();

        let mut dependencies = Vec::new();
        for callsite in &callsites {
            let mut sources: Vec<Source<'_>> = Vec::new();
            for arg in &callsite.arguments {
                use mir::Operand::*;
                match arg {
                    Copy(place) | Move(place) => {
                        for source in get_origins(place.local) {
                            sources.push(source);
                        }
                    }
                    Constant(cst) => {
                        if is_callable(cst.literal.ty) {
                            sources.push(Source::FunctionId(*cst.literal));
                        }
                    }
                }
            }

            use LocalCallType::*;
            let callee = match callsite.function {
                DirectCall(callee) => Callee::DirectCall(callee),
                LocalFunctionPtr(ptr) => Callee::LocalFunctionPtr(get_origins(ptr).collect()),
            };

            dependencies.push(CallerDependency { sources, callee });
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

    AllDependencies {
        functions: all_dependencies,
    }
}

// fn get_generic_name(tcx: ty::TyCtxt<'_>, def_id: DefId) -> String {
//     match tcx.opt_associated_item(def_id) {
//         Some(ty::AssocItem{def_id, ..}) => {
//             tcx.def_path_str(*def_id)
//         },
//         None => tcx.def_path_str(def_id),
//     }
// }

/// create and html-escaped string reprensentation for a given symbol
fn print_symbol(symbol: &Option<Symbol>) -> String {
    symbol
        .map(|s| html_escape::encode_text(&s.to_ident_string()).to_string())
        .unwrap_or_else(|| String::from("_"))
}

/// Write into `output` a testual reprensentation of `all_dependencies` in dot format
pub fn render_dependencies<'tcx, W: std::io::Write>(
    tcx: ty::TyCtxt<'tcx>,
    all_dependencies: AllDependencies<'tcx>,
    output: &mut W,
) -> std::io::Result<()> {
    //let crate_name = tcx.def_path_str(all_dependencies.crate_name);
    // writeln!(output, "digraph {} {{", crate_name)?;
    writeln!(output, "digraph {{")?;

    writeln!(output, "    subgraph {{")?;
    writeln!(
        output,
        "    node [ style=\"filled,solid\" width=10 height=1 color=black fillcolor=lightgrey ]"
    )?;
    writeln!(output)?;

    let mut internal_functions = HashSet::new();

    for (caller, function) in &all_dependencies.functions {
        if tcx.is_closure(*caller) {
            continue;
        }
        internal_functions.insert(caller);

        let caller_name = tcx.def_path_str(*caller);
        let escaped_caller_name = html_escape::encode_text(&caller_name);

        // TODO: add grouping by module? Maybe using a different color

        writeln!(output, "    \"{}\" [ label=<<table border=\"0\" cellpadding=\"2\" cellspacing=\"0\" cellborder=\"0\"><tr>", caller_name)?;
        writeln!(
            output,
            "        <td port=\"function\"><font color='red'>{}</font></td>",
            escaped_caller_name
        )?;
        // writeln!(output, "            <td>&lt;</td>")?;
        // writeln!(output, "            <td><font color='darkgreen'>Fct</font>: Fn()</td>")?;
        // writeln!(output, "            <td>&gt;</td>")?;
        writeln!(output, "        <td>(</td>")?;
        for (arg_id, SymbolAndType { symbol, ty }) in function.arguments.iter().enumerate() {
            let arg_id = arg_id + 1; // 0 is the return variable
            let symbol = print_symbol(symbol);
            let ty: ty::subst::GenericArg<'_> = (*ty).into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            let separation = if arg_id == function.arguments.len() {
                ""
            } else {
                ", "
            };
            writeln!(
                output,
                "            <td port=\"{}\">{}: <font color='darkgreen'>{}</font>{}</td>",
                arg_id, symbol, ty, separation
            )?;
        }
        writeln!(output, "        <td>)</td>")?;
        if !function.return_ty.is_unit() {
            let ty: ty::subst::GenericArg<'_> = function.return_ty.into();
            let ty = format!("{}", ty);
            let ty = html_escape::encode_text(&ty);
            let right_arrow = "&#8594;";
            writeln!(output, "        <td> {} </td>", right_arrow)?;
            writeln!(
                output,
                "        <td port=\"0\"><font color='darkgreen'>{}</font></td>",
                ty
            )?;
        }
        writeln!(output, "        </tr></table>>")?;
        writeln!(output, "    ]")?;
    }
    writeln!(output, "    }}")?;
    writeln!(output)?;
    writeln!(
        output,
        "    node [ style=\"filled,dotted\" width=10 height=1 color=black fillcolor=white ]"
    )?;
    writeln!(output)?;

    let mut indirect_dependencies = HashSet::new();
    for (caller, function) in all_dependencies.functions.iter() {
        let mut caller = *caller;
        if tcx.is_closure(caller) {
            caller = tcx.closure_base_def_id(caller);
        }

        let caller_name = tcx.def_path_str(caller);
        let mut callees = HashSet::new();
        for CallerDependency { sources, callee } in function.dependencies.iter() {
            for source in sources {
                use Source::*;
                match source {
                    FunctionId(source) => {
                        if !indirect_dependencies.contains(&(source, caller)) {
                            indirect_dependencies.insert((source, caller));

                            let source_name = tcx.mk_const(*source);
                            writeln!(
                                output,
                                "    \"{}\":function -> \"{}\"  [ color=blue arrowtail=empty ]",
                                source_name, caller_name
                            )?;
                        }
                    }
                    Argument(arg) => {
                        if is_callable(function.arguments[arg.as_usize() - 1].ty) {
                            writeln!(output, "    \"{}\" -> \"{}\":{} [ color=black arrowhead=empty style=solid ]", caller_name, caller_name, arg.as_usize())?;
                        }
                    }
                    ReturnVariable(_previous_callee) => {
                        // dependencies between return type add to much noice

                        // let previous_callee_name = tcx.def_path_str(*previous_callee);
                        // writeln!(output, "    \"{} to {}\" -> \"{} to {}\"  [ color=blue arrowtail=empty ]", caller_name, previous_callee_name, caller_name, callee_name)?;
                    }
                }
            }

            use Callee::*;
            match callee {
                DirectCall(callee) => {
                    // create only one arrow even if the same function is called multiple times
                    if !callees.contains(callee) {
                        callees.insert(*callee);

                        let style = if internal_functions.contains(callee) {
                            "solid"
                        } else {
                            "dotted"
                        };

                        let callee_name = tcx.def_path_str(*callee);
                        writeln!(
                            output,
                            "    \"{}\" -> \"{}\" [ color=black arrowhead=empty style={} ]",
                            caller_name, callee_name, style
                        )?;
                    }
                }
                LocalFunctionPtr(sources) => {
                    for source in sources {
                        use Source::*;
                        match source {
                            FunctionId(callee) => {
                                // FIXME: possible dupplicates edges if multiple function pointers
                                // points to the same function
                                let callee_name = tcx.mk_const(*callee);

                                // FIXME: detect if the callee could be an external function
                                let style = "solid";

                                writeln!(
                                    output,
                                    "    \"{}\" -> \"{}\" [ color=black arrowhead=empty style={} ]",
                                    caller_name, callee_name, style
                                )?;
                            }
                            Argument(arg) => {
                                if is_callable(function.arguments[arg.as_usize() - 1].ty) {
                                    writeln!(output, "    \"{}\" -> \"{}\":{} [ color=black arrowhead=empty style=solid ]", caller_name, caller_name, arg.as_usize())?;
                                }
                            }
                            ReturnVariable(_previous_callee) => {
                                eprintln!("warning: call to a function pointer returned by another function was not displayed in {}", caller_name);
                            }
                        }
                    }
                }
            }
        }
        for source in function.return_deps.iter() {
            use Source::*;
            match source {
                FunctionId(source) => {
                    let source_name = tcx.mk_const(*source);

                    // WTF: it seems that source_name can be printed as "\"crate-name\""?
                    // ```
                    // ""crate-name"":function -> "opts to stable"  [ color=blue arrowtail=empty ]
                    // ```
                    writeln!(
                        output,
                        "    \"{}\":function -> \"{}\":0  [ color=blue arrowtail=empty ]",
                        source_name, caller_name
                    )?;
                }
                Argument(_arg) => {
                    // dependencies from arguments add to much noice

                    // writeln!(output, "    \"{}\":{} -> \"{}\":0  [ color=blue arrowtail=empty ]", caller_name, arg.as_usize(), caller_name)?;
                }
                ReturnVariable(_previous_callee) => {
                    // dependencies from other return type add to much noice

                    // if caller != previous_callee {
                    //     let previous_callee_name = tcx.def_path_str(*previous_callee);
                    //     writeln!(output, "    \"{} to {}\" -> \"{}\":0  [ color=blue arrowtail=empty ]", caller_name, previous_callee_name, caller_name)?;
                    // }
                }
            }
        }
    }

    writeln!(output, "}}")?;

    Ok(())
}
