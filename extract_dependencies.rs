use crate::rustc_middle::mir::visit::Visitor;
use crate::rustc_middle::ty::{DefIdTree, Ty};
use itertools::Itertools;
use rustc_hir::def_id::DefId;
use rustc_index::vec::IndexVec;
use rustc_middle::mir;
use rustc_middle::mir::terminator::*;
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::collections::HashSet;

// ************************************************************ //
// The output of the analysis

type LocalCallee = usize;

/// Store all the dependencies between one function and its callee
pub struct FunctionDependencies<'tcx> {
    /// name of the function
    name: mir::Constant<'tcx>,
    /// name and type of all the arguments and the returned value to this
    /// function
    arguments: IndexVec<mir::Local, (Option<mir::Constant<'tcx>>, Ty<'tcx>)>,
    /// List of all call-sites inside the body of this function
    callee: IndexVec<LocalCallee, Callee<'tcx>>,
}

/// Store the name of a called function and the source of all of its arguments
pub struct Callee<'tcx> {
    /// name of the called function
    name: mir::Constant<'tcx>,
    /// source (possibly over-approximated) of the source of each argument to
    /// this called function
    arguments: IndexVec<mir::Local, HashSet<Origin<'tcx>>>,
}

/// Express one of the possible source of a given argument
pub enum Origin<'tcx> {
    /// A literal expression
    Literal(mir::Constant<'tcx>),
    /// An argument of the function being analyzed
    FromArgument(mir::Local),
    /// The return value of a another callee
    FromReturn(LocalCallee),
}

// ************************************************************ //
// Extract relationship between all the locals in a function

// FIXME: -> IndexVec<mir::Local, Vec<mir::Local>>
fn depends_from_args(mir: &mir::Body) -> IndexVec<mir::Local, bool> {
    // TODO: extract the relationship between the local_variable and the argument to the
    // function, an not just the boolean information that it cames from an argument

    // +1 because of the return value
    let local_count = mir.arg_count + mir.local_decls.len() + 1;

    let mut dependencies: IndexVec<mir::Local, Vec<mir::Local>> = (0..local_count)
        .map(|_| Vec::new())
        .collect();
    for basic_block in mir.basic_blocks() {
        for statement in &basic_block.statements {

            let ignore = || {};
            let mut add_dependency = |lvalue: mir::Local, rvalue: mir::Place<'_>| {
                if let Some(rvalue) = rvalue.local_or_deref_local() {
                    dependencies[lvalue].push(rvalue);
                }
            };

            match &statement.kind {
                mir::StatementKind::Assign(assignment) => {
                    let (lvalue, rvalue) = &**assignment;
                    let lvalue = lvalue.as_local().unwrap();

                    match rvalue {
                        mir::Rvalue::Use(op) => {
                            op.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::Repeat(op, _) => {
                            op.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::Ref(_, _, rvalue) => {
                            add_dependency(lvalue, *rvalue);
                        },
                        mir::Rvalue::ThreadLocalRef(_) => {
                            () // TODO:add support to threadlocal;
                        },
                        mir::Rvalue::AddressOf(_, rvalue) => {
                            add_dependency(lvalue, *rvalue);
                        },
                        mir::Rvalue::Len(_) => {
                            ignore();
                        },
                        mir::Rvalue::Cast(_, op, _) => {
                            op.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::BinaryOp(_, op1, op2) => {
                            op1.place().map(|rvalue| add_dependency(lvalue, rvalue));
                            op2.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::CheckedBinaryOp(_, op1, op2) => {
                            op1.place().map(|rvalue| add_dependency(lvalue, rvalue));
                            op2.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::NullaryOp(_, _) => {
                            ignore();
                        },
                        mir::Rvalue::UnaryOp(_, op) => {
                            op.place().map(|rvalue| add_dependency(lvalue, rvalue));
                        },
                        mir::Rvalue::Discriminant(_) => {
                            ignore();
                        },
                        mir::Rvalue::Aggregate(_, operands) => {
                            for op in operands {
                                op.place().map(|rvalue| add_dependency(lvalue, rvalue));
                            }
                        },
                    }
                },
                mir::StatementKind::LlvmInlineAsm(assembly) => {
                    let rustc_middle::mir::LlvmInlineAsm{asm: _, outputs, inputs} = &**assembly;
                    let inputs = &**inputs;
                    let outputs = &**outputs;
                    for (_, lvalue) in inputs {
                        if let Some(lvalue) = lvalue.place() {
                            let lvalue = lvalue.as_local().unwrap();
                            for rvalue in outputs {
                                add_dependency(lvalue, *rvalue);
                            }
                        }
                    }
                },
                mir::StatementKind::FakeRead(..) 
                | mir::StatementKind::SetDiscriminant {..} 
                | mir::StatementKind::StorageLive(..) 
                | mir::StatementKind::StorageDead(..) 
                | mir::StatementKind::Retag(..) 
                | mir::StatementKind::AscribeUserType(..) 
                | mir::StatementKind::Coverage(..) 
                | mir::StatementKind::Nop => {
                    ignore();
                },
            }
        }
    }

    let mut depends_from_args: IndexVec<mir::Local, Option<bool>> = (0..local_count)
        .map(|_| None)
        .collect();
    for arg in mir.args_iter() {
        depends_from_args[arg] = Some(true);
    }
    while !depends_from_args.iter().all(Option::is_some) {
        for (lvalue, dependencies) in dependencies.iter_enumerated() {
            if depends_from_args[lvalue] == None {
                if dependencies.iter().any(|rvalue| depends_from_args[*rvalue] == Some(true)) {
                    depends_from_args[lvalue] = Some(true);
                } else if dependencies.iter().all(|rvalue| depends_from_args[*rvalue] == Some(false)) {
                    // Note: In case dependencies is empty, the condition is also true
                    // No dependencies => it's a constant
                    depends_from_args[lvalue] = Some(false);
                }
            }
        }
    }
    let depends_from_args: IndexVec<mir::Local, bool> = depends_from_args
        .iter()
        .map(|has_dependency| has_dependency == &Some(true))
        .collect();
    depends_from_args
}

// ************************************************************ //
// Extracting the informations about all function call

struct SearchFunctionCall<'tcx, 'dependencies> {
    inner_functions: Vec<(mir::Operand<'tcx>, bool)>,
    depends_from_args: &'dependencies IndexVec<mir::Local, bool>,
}

impl<'tcx, 'dependencies> SearchFunctionCall<'tcx, 'dependencies> {
    fn new(depends_from_args: &'dependencies IndexVec<mir::Local, bool>) -> Self {
        SearchFunctionCall {
            inner_functions: Vec::new(),
            depends_from_args
        }
    }
}


impl<'tcx, 'dependencies> rustc_middle::mir::visit::Visitor<'tcx> for SearchFunctionCall<'tcx, 'dependencies> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _location: mir::Location) {
        if let TerminatorKind::Call{func, args, ..} = &terminator.kind {
            let depends_from_caller = args
                .iter()
                .any(|arg| {
                    arg
                        .place()
                        .map(|p| {
                            p.local_or_deref_local().map(|local| self.depends_from_args[local])
                        })
                        .flatten()
                        .unwrap_or(false)
                });
            self.inner_functions.push((func.clone(), depends_from_caller));
        }
    }
}

// ************************************************************ //
// Utilities

/// Return the name of the module of a given function
fn get_module(tcx: TyCtxt<'_>, function: DefId) -> String {
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
    crate_name + &def_path.data.iter().map(|m| format!("{}", m)).join("::")
}

#[derive(Clone)]
enum Function {
    Direct(DefId, bool),
    Monomorphized(DefId, String, bool),
}

pub fn extract_dependencies(tcx: TyCtxt<'_>) {
    let mut functions: HashSet<DefId> = HashSet::new();
    let mut monomorphized_functions: HashSet<(DefId, String)> = HashSet::new();
    let mut dependencies: Vec<(DefId, Function)> = Vec::new();

    for caller in tcx.body_owners() {
        let mir = tcx.mir_built(rustc_middle::ty::WithOptConstParam {
            did: caller,
            const_param_did: tcx.opt_const_param_of(caller)
        });
        let mir = &mir.borrow();

        let depends_from_args = depends_from_args(&mir);

        let mut subfunctions = SearchFunctionCall::new(&depends_from_args);
        subfunctions.visit_body(mir);

        let caller = caller.to_def_id();
        functions.insert(caller);

        for (subfunction, depends_from_caller) in subfunctions.inner_functions {
            // TODO: take a look at
            // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/ty/struct.TyCtxt.html#method.upstream_monomorphizations_for
            let callee_id = if let rustc_middle::ty::FnDef(def_id, _) = subfunction.constant().unwrap().literal.ty.kind() {
                *def_id
            } else {
                unreachable!();
            };
            functions.insert(callee_id);

            let callee_str = tcx.def_path_str(callee_id);
            let full_name = format!("{:?}", subfunction);
            let monomorphized_call = full_name != callee_str;
            if monomorphized_call {
                monomorphized_functions.insert((callee_id, full_name.clone()));
                dependencies.push((caller, Function::Monomorphized(callee_id, full_name, depends_from_caller)));
            } else {
                dependencies.push((caller, Function::Direct(callee_id, depends_from_caller)));
            }
        }
    }

    // Group item by module
    // TODO: create a hierarchy of module
    let modules: HashSet<_> = functions
        .iter()
        .map(|&f| get_module(tcx, f))
        .collect();
    let modules: HashMap<String, usize> = modules
        .into_iter()
        .enumerate()
        .map(|(id, name)| (name, id))
        .collect();

    let functions = {
        let mut _functions: HashMap<String, Vec<DefId>> = modules
            .iter()
            .map(|(name, _)| (name.clone(), Vec::new()))
            .collect();
        for function in functions {
            _functions.get_mut(&get_module(tcx, function)).unwrap().push(function);
        }
        for &(id, _) in &monomorphized_functions {
            _functions.get_mut(&get_module(tcx, id)).unwrap().push(id);
        }
        _functions
    };

    let monomorphized_functions = {
        let mut _functions: HashMap<String, Vec<String>> = modules
            .iter()
            .map(|(name, _)| (name.clone(), Vec::new()))
            .collect();
        for (id, full_name) in monomorphized_functions {
            _functions.get_mut(&get_module(tcx, id)).unwrap().push(full_name);
        }
        _functions
    };

    eprintln!("strict digraph {{");

    for (module_name, module_id) in &modules {
        eprintln!("    subgraph cluster{} {{", module_id);
        if module_name.is_empty() {
            // it's the root of the crate
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
            eprintln!("        \"{}\" [shape=none]", tcx.def_path_str(function));
        }

        // create virtual nodes for monomorphized call");
        for full_name in &monomorphized_functions[module_name] {
            eprintln!("        \"{}\" [label=\"\"; fixedsize=\"false\"; width=0; height=0; shape=none]", full_name);
        }

        eprintln!("    }}");
    }

    eprintln!("\n    // dependency graph");
    for (caller, callee) in dependencies {
        match callee {
            Function::Direct(callee_id, depends_from_caller) => {
                let caller = tcx.def_path_str(caller);
                let callee_str = tcx.def_path_str(callee_id);
                eprintln!("    \"{}\" -> \"{}\"", caller, callee_str);
                if depends_from_caller {
                    eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", callee_str, caller);
                }
            },
            Function::Monomorphized(callee_id, full_name, depends_from_caller) => {
                let caller = tcx.def_path_str(caller);
                let callee_str = tcx.def_path_str(callee_id);
                eprintln!("    \"{}\" -> \"{}\" [arrowhead=none]", caller, full_name);
                eprintln!("    \"{}\" -> \"{}\"", full_name, callee_str);
                if depends_from_caller {
                    eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", callee_str, full_name);
                    eprintln!("    \"{}\" -> \"{}\" [style=dotted; constraint=false; arrowhead=none]", full_name, caller);
                }
            }
        }
    }

    eprintln!("}}");
}
