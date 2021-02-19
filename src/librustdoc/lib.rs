#![allow(dead_code)]
#![allow(unused_imports)]

#![doc(
    html_root_url = "https://doc.rust-lang.org/nightly/",
    html_playground_url = "https://play.rust-lang.org/"
)]
#![allow(dead_code)]
#![feature(array_methods)]
#![feature(bool_to_option)]
#![feature(box_patterns)]
#![feature(box_syntax)]
#![feature(crate_visibility_modifier)]
#![feature(default_free_fn)]
#![feature(in_band_lifetimes)]
#![feature(iter_intersperse)]
#![feature(never_type)]
#![feature(nll)]
#![feature(once_cell)]
#![feature(or_patterns)]
#![feature(rustc_private)]
#![feature(str_split_once)]
#![feature(test)]
#![feature(type_ascription)]
#![recursion_limit = "256"]
#![deny(rustc::internal)]

#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate tracing;

// N.B. these need `extern crate` even in 2018 edition
// because they're loaded implicitly from the sysroot.
// The reason they're loaded from the sysroot is because
// the rustdoc artifacts aren't stored in rustc's cargo target directory.
// So if `rustc` was specified in Cargo.toml, this would spuriously rebuild crates.
//
// Dependencies listed in Cargo.toml do not need `extern crate`.
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_attr;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_expand;
extern crate rustc_feature;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_infer;
extern crate rustc_interface;
extern crate rustc_lexer;
extern crate rustc_lint;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir;
extern crate rustc_parse;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span as rustc_span;
extern crate rustc_target;
extern crate rustc_trait_selection;
extern crate rustc_typeck;
extern crate test as testing;

use std::default::Default;
use std::env;
use std::process;

use rustc_errors::ErrorReported;
use rustc_session::config::{make_crate_type_option, ErrorOutputType, RustcOptGroup};
use rustc_session::getopts;
use rustc_session::{early_error, early_warn};

#[macro_use]
mod externalfiles;

mod clean;
mod config;
mod core;
mod docfs;
mod doctree;
#[macro_use]
mod error;
mod extract_dependencies;
mod doctest;
mod fold;
mod formats;
// used by the error-index generator, so it needs to be public
pub mod html;
mod json;
mod markdown;
mod passes;
mod theme;
mod visit_ast;
mod visit_lib;

pub fn main() {
    rustc_driver::set_sigpipe_handler();
    rustc_driver::install_ice_hook();
    rustc_driver::init_env_logger("RUSTDOC_LOG");
    let exit_code = rustc_driver::catch_with_exit_code(|| match get_args() {
        Some(args) => main_args(&args),
        _ => Err(ErrorReported),
    });
    process::exit(exit_code);
}

/// Taken from
/// https://github.com/rust-lang/miri/blob/master/src/bin/miri.rs
/// Returns the "default sysroot" that will be used if no `--sysroot` flag is set.
/// Should be a compile-time constant.
fn compile_time_sysroot() -> Option<String> {
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc_session.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc_session would
    // end up somewhere in the build dir (see `get_or_default_sysroot`).
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    if option_env!("RUSTC_STAGE").is_some() {
        // This is being built as part of rustc, and gets shipped with rustup.
        // We can rely on the sysroot computation in librustc_session.
        return None;
    }
    // For builds outside rustc, we need to ensure that we got a sysroot
    // that gets used as a default.  The sysroot computation in librustc_session would
    // end up somewhere in the build dir (see `get_or_default_sysroot`).
    // Taken from PR <https://github.com/Manishearth/rust-clippy/pull/911>.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    Some(match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("To build cargo-callgraph without rustup, set the `RUST_SYSROOT` env var at build time")
            .to_owned(),
    })
}

fn get_args() -> Option<Vec<String>> {
    env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string()
                .map_err(|arg| {
                    early_warn(
                        ErrorOutputType::default(),
                        &format!("Argument {} is not valid Unicode: {:?}", i, arg),
                    );
                })
                .ok()
        })
        .collect::<Option<_>>()
        .map(|mut args: Vec<String>| {
            // Make sure we use the right default sysroot. The default sysroot is wrong,
            // because `get_or_default_sysroot` in `librustc_session` bases that on `current_exe`.
            //
            // Make sure we always call `compile_time_sysroot` as that also does some sanity-checks
            // of the environment we were built in.
            // FIXME: Ideally we'd turn a bad build env into a compile-time error via CTFE or so.
            if let Some(sysroot) = compile_time_sysroot() {
                let sysroot_flag = "--sysroot";
                if !args.iter().any(|e| e == sysroot_flag) {
                    // We need to overwrite the default that librustc_session would compute.
                    args.push(sysroot_flag.to_owned());
                    args.push(sysroot);
                }
            }

            args
        })
}

fn opts() -> Vec<RustcOptGroup> {
    let stable: fn(_, fn(&mut getopts::Options) -> &mut _) -> _ = RustcOptGroup::stable;
    let unstable: fn(_, fn(&mut getopts::Options) -> &mut _) -> _ = RustcOptGroup::unstable;
    vec![
        stable("h", |o| o.optflag("h", "help", "show this help message")),
        stable("V", |o| o.optflag("V", "version", "print rustdoc's version")),
        stable("v", |o| o.optflag("v", "verbose", "use verbose output")),
        stable("r", |o| {
            o.optopt("r", "input-format", "the input type of the specified file", "[rust]")
        }),
        stable("w", |o| o.optopt("w", "output-format", "the output type to write", "[html]")),
        stable("o", |o| o.optopt("o", "output", "where to place the output", "PATH")),
        stable("crate-name", |o| {
            o.optopt("", "crate-name", "specify the name of this crate", "NAME")
        }),
        make_crate_type_option(),
        stable("L", |o| {
            o.optmulti("L", "library-path", "directory to add to crate search path", "DIR")
        }),
        stable("cfg", |o| o.optmulti("", "cfg", "pass a --cfg to rustc", "")),
        stable("extern", |o| o.optmulti("", "extern", "pass an --extern to rustc", "NAME[=PATH]")),
        unstable("extern-html-root-url", |o| {
            o.optmulti("", "extern-html-root-url", "base URL to use for dependencies", "NAME=URL")
        }),
        stable("plugin-path", |o| o.optmulti("", "plugin-path", "removed", "DIR")),
        stable("C", |o| {
            o.optmulti("C", "codegen", "pass a codegen option to rustc", "OPT[=VALUE]")
        }),
        stable("passes", |o| {
            o.optmulti(
                "",
                "passes",
                "list of passes to also run, you might want to pass it multiple times; a value of \
                 `list` will print available passes",
                "PASSES",
            )
        }),
        stable("plugins", |o| o.optmulti("", "plugins", "removed", "PLUGINS")),
        stable("no-default", |o| o.optflag("", "no-defaults", "don't run the default passes")),
        stable("document-private-items", |o| {
            o.optflag("", "document-private-items", "document private items")
        }),
        unstable("document-hidden-items", |o| {
            o.optflag("", "document-hidden-items", "document items that have doc(hidden)")
        }),
        stable("test", |o| o.optflag("", "test", "run code examples as tests")),
        stable("test-args", |o| {
            o.optmulti("", "test-args", "arguments to pass to the test runner", "ARGS")
        }),
        unstable("test-run-directory", |o| {
            o.optopt(
                "",
                "test-run-directory",
                "The working directory in which to run tests",
                "PATH",
            )
        }),
        stable("target", |o| o.optopt("", "target", "target triple to document", "TRIPLE")),
        stable("markdown-css", |o| {
            o.optmulti(
                "",
                "markdown-css",
                "CSS files to include via <link> in a rendered Markdown file",
                "FILES",
            )
        }),
        stable("html-in-header", |o| {
            o.optmulti(
                "",
                "html-in-header",
                "files to include inline in the <head> section of a rendered Markdown file \
                 or generated documentation",
                "FILES",
            )
        }),
        stable("html-before-content", |o| {
            o.optmulti(
                "",
                "html-before-content",
                "files to include inline between <body> and the content of a rendered \
                 Markdown file or generated documentation",
                "FILES",
            )
        }),
        stable("html-after-content", |o| {
            o.optmulti(
                "",
                "html-after-content",
                "files to include inline between the content and </body> of a rendered \
                 Markdown file or generated documentation",
                "FILES",
            )
        }),
        unstable("markdown-before-content", |o| {
            o.optmulti(
                "",
                "markdown-before-content",
                "files to include inline between <body> and the content of a rendered \
                 Markdown file or generated documentation",
                "FILES",
            )
        }),
        unstable("markdown-after-content", |o| {
            o.optmulti(
                "",
                "markdown-after-content",
                "files to include inline between the content and </body> of a rendered \
                 Markdown file or generated documentation",
                "FILES",
            )
        }),
        stable("markdown-playground-url", |o| {
            o.optopt("", "markdown-playground-url", "URL to send code snippets to", "URL")
        }),
        stable("markdown-no-toc", |o| {
            o.optflag("", "markdown-no-toc", "don't include table of contents")
        }),
        stable("e", |o| {
            o.optopt(
                "e",
                "extend-css",
                "To add some CSS rules with a given file to generate doc with your \
                 own theme. However, your theme might break if the rustdoc's generated HTML \
                 changes, so be careful!",
                "PATH",
            )
        }),
        unstable("Z", |o| {
            o.optmulti("Z", "", "internal and debugging options (only on nightly build)", "FLAG")
        }),
        stable("sysroot", |o| o.optopt("", "sysroot", "Override the system root", "PATH")),
        unstable("playground-url", |o| {
            o.optopt(
                "",
                "playground-url",
                "URL to send code snippets to, may be reset by --markdown-playground-url \
                 or `#![doc(html_playground_url=...)]`",
                "URL",
            )
        }),
        unstable("display-warnings", |o| {
            o.optflag("", "display-warnings", "to print code warnings when testing doc")
        }),
        stable("crate-version", |o| {
            o.optopt("", "crate-version", "crate version to print into documentation", "VERSION")
        }),
        unstable("sort-modules-by-appearance", |o| {
            o.optflag(
                "",
                "sort-modules-by-appearance",
                "sort modules by where they appear in the program, rather than alphabetically",
            )
        }),
        stable("default-theme", |o| {
            o.optopt(
                "",
                "default-theme",
                "Set the default theme. THEME should be the theme name, generally lowercase. \
                 If an unknown default theme is specified, the builtin default is used. \
                 The set of themes, and the rustdoc built-in default, are not stable.",
                "THEME",
            )
        }),
        unstable("default-setting", |o| {
            o.optmulti(
                "",
                "default-setting",
                "Default value for a rustdoc setting (used when \"rustdoc-SETTING\" is absent \
                 from web browser Local Storage). If VALUE is not supplied, \"true\" is used. \
                 Supported SETTINGs and VALUEs are not documented and not stable.",
                "SETTING[=VALUE]",
            )
        }),
        stable("theme", |o| {
            o.optmulti(
                "",
                "theme",
                "additional themes which will be added to the generated docs",
                "FILES",
            )
        }),
        stable("check-theme", |o| {
            o.optmulti("", "check-theme", "check if given theme is valid", "FILES")
        }),
        unstable("resource-suffix", |o| {
            o.optopt(
                "",
                "resource-suffix",
                "suffix to add to CSS and JavaScript files, e.g., \"light.css\" will become \
                 \"light-suffix.css\"",
                "PATH",
            )
        }),
        stable("edition", |o| {
            o.optopt(
                "",
                "edition",
                "edition to use when compiling rust code (default: 2015)",
                "EDITION",
            )
        }),
        stable("color", |o| {
            o.optopt(
                "",
                "color",
                "Configure coloring of output:
                                          auto   = colorize, if output goes to a tty (default);
                                          always = always colorize output;
                                          never  = never colorize output",
                "auto|always|never",
            )
        }),
        stable("error-format", |o| {
            o.optopt(
                "",
                "error-format",
                "How errors and other messages are produced",
                "human|json|short",
            )
        }),
        stable("json", |o| {
            o.optopt("", "json", "Configure the structure of JSON diagnostics", "CONFIG")
        }),
        unstable("disable-minification", |o| {
            o.optflag("", "disable-minification", "Disable minification applied on JS files")
        }),
        stable("warn", |o| o.optmulti("W", "warn", "Set lint warnings", "OPT")),
        stable("allow", |o| o.optmulti("A", "allow", "Set lint allowed", "OPT")),
        stable("deny", |o| o.optmulti("D", "deny", "Set lint denied", "OPT")),
        stable("forbid", |o| o.optmulti("F", "forbid", "Set lint forbidden", "OPT")),
        stable("cap-lints", |o| {
            o.optmulti(
                "",
                "cap-lints",
                "Set the most restrictive lint level. \
                 More restrictive lints are capped at this \
                 level. By default, it is at `forbid` level.",
                "LEVEL",
            )
        }),
        unstable("index-page", |o| {
            o.optopt("", "index-page", "Markdown file to be used as index page", "PATH")
        }),
        unstable("enable-index-page", |o| {
            o.optflag("", "enable-index-page", "To enable generation of the index page")
        }),
        unstable("static-root-path", |o| {
            o.optopt(
                "",
                "static-root-path",
                "Path string to force loading static files from in output pages. \
                 If not set, uses combinations of '../' to reach the documentation root.",
                "PATH",
            )
        }),
        unstable("disable-per-crate-search", |o| {
            o.optflag(
                "",
                "disable-per-crate-search",
                "disables generating the crate selector on the search box",
            )
        }),
        unstable("persist-doctests", |o| {
            o.optopt(
                "",
                "persist-doctests",
                "Directory to persist doctest executables into",
                "PATH",
            )
        }),
        unstable("show-coverage", |o| {
            o.optflag(
                "",
                "show-coverage",
                "calculate percentage of public items with documentation",
            )
        }),
        unstable("enable-per-target-ignores", |o| {
            o.optflag(
                "",
                "enable-per-target-ignores",
                "parse ignore-foo for ignoring doctests on a per-target basis",
            )
        }),
        unstable("runtool", |o| {
            o.optopt(
                "",
                "runtool",
                "",
                "The tool to run tests with when building for a different target than host",
            )
        }),
        unstable("runtool-arg", |o| {
            o.optmulti(
                "",
                "runtool-arg",
                "",
                "One (of possibly many) arguments to pass to the runtool",
            )
        }),
        unstable("test-builder", |o| {
            o.optopt("", "test-builder", "The rustc-like binary to use as the test builder", "PATH")
        }),
        unstable("check", |o| o.optflag("", "check", "Run rustdoc checks")),
    ]
}

fn usage(argv0: &str) {
    let mut options = getopts::Options::new();
    for option in opts() {
        (option.apply)(&mut options);
    }
    println!("{}", options.usage(&format!("{} [options] <input>", argv0)));
    println!("More information available at https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html")
}

/// A result type used by several functions under `main()`.
type MainResult = Result<(), ErrorReported>;

fn main_args(args: &[String]) -> MainResult {
    let mut options = getopts::Options::new();
    for option in opts() {
        (option.apply)(&mut options);
    }
    let matches = match options.parse(&args[1..]) {
        Ok(m) => m,
        Err(err) => {
            early_error(ErrorOutputType::default(), &err.to_string());
        }
    };

    // Note that we discard any distinction between different non-zero exit
    // codes from `from_matches` here.
    let options = match config::Options::from_matches(&matches) {
        Ok(opts) => opts,
        Err(code) => return if code == 0 { Ok(()) } else { Err(ErrorReported) },
    };
    rustc_interface::util::setup_callbacks_and_run_in_thread_pool_with_globals(
        options.edition,
        1, // this runs single-threaded, even in a parallel compiler
        &None,
        move || main_options(options),
    )
}

fn wrap_return(diag: &rustc_errors::Handler, res: Result<(), String>) -> MainResult {
    match res {
        Ok(()) => Ok(()),
        Err(err) => {
            diag.struct_err(&err).emit();
            Err(ErrorReported)
        }
    }
}

fn main_options(options: config::Options) -> MainResult {
    let diag = core::new_handler(options.error_format, None, &options.debugging_opts);

    match (options.should_test, options.markdown_input()) {
        (true, true) => return wrap_return(&diag, markdown::test(options)),
        (true, false) => return doctest::run(options),
        (false, true) => {
            return wrap_return(
                &diag,
                markdown::render(&options.input, options.render_options, options.edition),
            );
        }
        (false, false) => {}
    }

    // Interpret the input file as a rust source file, passing it through the
    // compiler all the way through the analysis passes.
    extract_dependencies::run_core(options);
    Ok(())
}
