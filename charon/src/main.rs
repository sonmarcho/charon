#![feature(rustc_private, register_tool)]
#![feature(box_syntax, box_patterns)]
#![feature(is_some_with)]
#![feature(cell_leak)] // For Ref::leak
// For rustdoc: prevents overflows
#![recursion_limit = "256"]

extern crate env_logger;
extern crate hashlink;
extern crate im;
extern crate linked_hash_set;
extern crate log;
extern crate rustc_ast;
extern crate rustc_borrowck;
extern crate rustc_const_eval;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_mir_transform;
extern crate rustc_monomorphize;
extern crate rustc_resolve;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate take_mut;

#[macro_use]
mod common;
mod assumed;
mod divergent;
mod expressions;
mod expressions_utils;
mod extract_global_assignments;
mod formatter;
mod generics;
mod get_mir;
mod graphs;
mod id_vector;
mod im_ast;
mod im_ast_utils;
mod im_to_llbc;
mod insert_assign_return_unit;
mod llbc_ast;
mod llbc_ast_utils;
mod llbc_export;
mod names;
mod names_utils;
mod reconstruct_asserts;
mod regions_hierarchy;
mod register;
mod regularize_constant_adts;
mod remove_unused_locals;
mod reorder_decls;
mod rust_to_local_ids;
mod simplify_ops;
mod translate_functions_to_im;
mod translate_types;
mod types;
mod types_utils;
mod values;
mod values_utils;

use log::info;
use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_interface::{interface::Compiler, Queries};
use rustc_middle::ty::TyCtxt;
use rustc_session::Session;
use serde::Deserialize;
use serde_json;
use std::collections::{HashMap, HashSet};
use std::fmt::{Display, Error, Formatter};
use std::iter::FromIterator;
use std::path::PathBuf;
use structopt::StructOpt;

struct ToInternal {
    dest_dir: Option<PathBuf>,
    source_file: PathBuf,
    no_code_duplication: bool,
    opaque_modules: Vec<String>,
}

impl Callbacks for ToInternal {
    /// We have to be careful here: we can plug ourselves at several places
    /// (after parsing, after expansion, after analysis). However, the MIR is
    /// modified in place: this means that if we at some point we compute, say,
    /// the promoted MIR, it is possible to query the optimized MIR (because
    /// optimized MIR is further down in the compilation process). However,
    /// it is not possible to query, say, the built MIR (which results from
    /// the conversion to HIR to MIR) because it has been lost.
    /// For this reason, and as we may want to plug ourselves at different
    /// phases of the compilation process, we query the context as early as
    /// possible (i.e., after parsing). See [get_mir].
    fn after_parsing<'tcx>(&mut self, c: &Compiler, queries: &'tcx Queries<'tcx>) -> Compilation {
        queries
            .global_ctxt()
            .unwrap()
            .peek_mut()
            .enter(|tcx| {
                let session = c.session();
                translate(session, tcx, &self)
            })
            .unwrap();
        Compilation::Stop
    }
}

/// Initialize the logger. We use a custom initialization to add some
/// useful debugging information, including the line number in the file.
fn initialize_logger() {
    use chrono::offset::Local;
    use env_logger::fmt::Color;
    use env_logger::{Builder, Env};
    use std::io::Write;

    // Create a default environment, by using the environment variables.
    // We do this to let the user choose the log level (i.e.: trace,
    // debug, warning, etc.)
    let env = Env::default();
    // If the log level is not set, set it to "info"
    let env = env.default_filter_or("info");

    // Initialize the log builder from the environment we just created
    let mut builder = Builder::from_env(env);

    // Modify the output format - we add the line number
    builder.format(|buf, record| {
        // Retreive the path (CRATE::MODULE) and the line number
        let path = match record.module_path() {
            Some(s) => s,
            None => "",
        };
        let line = match record.line() {
            Some(l) => l.to_string(),
            None => "".to_string(),
        };

        // Style for the brackets (change the color)
        let mut bracket_style = buf.style();
        bracket_style.set_color(Color::Rgb(120, 120, 120));

        writeln!(
            buf,
            "{}{} {} {}:{}{} {}",
            bracket_style.value("["),
            Local::now().format("%H:%M:%S"), // Rk.: use "%Y-%m-%d" to also have the date
            buf.default_styled_level(record.level()), // Print the level with colors
            path,
            line,
            bracket_style.value("]"),
            record.args()
        )
    });

    builder.init();
}

/// Charon expects the project to have been built in debug mode before performing
/// extraction: `cargo build`. In particular, it will look for already compiled
/// external dependencies in the target directory (`/target/debug/deps/`, usually).
// This structure is used to store the command-line instructions.
// We automatically derive a command-line parser based on this structure.
// Note that the doc comments are used to generate the help message when using
// `--help`.
//
// TODO: give the possibility of changing the crate name.
#[derive(StructOpt)]
#[structopt(name = "Charon")]
struct CliOpts {
    /// The input file (the entry point of the crate to extract)
    #[structopt(parse(from_os_str))]
    input_file: PathBuf,
    /// The destination directory, if we don't want to generate the output
    /// .llbc files in the same directory as the input .rs files.
    #[structopt(long = "dest", parse(from_os_str))]
    dest_dir: Option<PathBuf>,
    /// If activated, use Polonius' non-lexical lifetimes (NLL) analysis.
    /// Otherwise, use the standard borrow checker.
    #[structopt(long = "nll")]
    use_polonius: bool,
    #[structopt(
        long = "no-code-duplication",
        help = "Check that no code duplication happens during control-flow reconstruction
of the MIR code.

This is only used to make sure the reconstructed code is of good quality.
For instance, if we have the following CFG in MIR:
  ```
  b0: switch x [true -> goto b1; false -> goto b2]
  b1: y := 0; goto b3
  b2: y := 1; goto b3
  b3: return y      
  ```

We want to reconstruct the control-flow as:
  ```
  if x then { y := 0; } else { y := 1 };
  return y;
  ```

But if we don't do this reconstruction correctly, we might duplicate
the code starting at b3:
  ```
  if x then { y := 0; return y; } else { y := 1; return y; }
  ```

When activating this flag, we check that no such things happen.

Also note that it is sometimes not possible to prevent code duplication,
if the original Rust looks like this for instance:
  ```
  match x with
  | E1(y,_) | E2(_,y) => { ... } // Some branches are \"fused\"
  | E3 => { ... }
  ```

The reason is that assignments are introduced when desugaring the pattern
matching, and those assignments are specific to the variant on which we pattern
match (the `E1` branch performs: `y := (x as E1).0`, while the `E2` branch
performs: `y := (x as E2).1`). Producing a better reconstruction is non-trivial.
"
    )]
    no_code_duplication: bool,
    /// A list of modules of the extracted crate that we consider as opaque: we
    /// extract only the signature information, without the definition content
    /// (of the functions, types, etc.).
    #[structopt(long = "opaque")]
    opaque: Vec<String>,
}

// The following helpers are used to read crate manifests (the `Cargo.toml` files),
// and were adapated from [hacspec](https://github.com/hacspec/).

/// We ignore some fields:
/// - source: String
/// - req: String
/// - rename: Option<String>
/// - optional: bool
/// - uses_default_features: bool
/// - features: Vec<?>
/// - target: Option<?>
/// - registry: Opion<?>
#[derive(Debug, Deserialize, Clone)]
struct Dependency {
    name: String,
    kind: Option<String>,
}

/// We ignore some fields:
/// - edition: string
/// - doctest: bool
/// - test: bool
/// TODO: remove?
#[derive(Debug, Deserialize, Clone)]
struct Target {
    #[allow(dead_code)]
    name: String,
    kind: Vec<String>,
    #[allow(dead_code)]
    crate_types: Vec<String>,
    #[allow(dead_code)]
    src_path: String,
}

#[derive(Debug, Deserialize, Clone)]
/// We ignore some fields:
/// - version: string
/// - license: Option<String>
/// - license_file: Option<String>
/// - description: Option<String>
/// - source: Option<String>
/// - features: ?
/// - metadata: Option<?>
/// - publish: Option<?>
/// - authors: Vec<String>
/// - categories: Vec<?>
/// - keywords: Vec<?>
/// - readme: Option<?>
/// - repository: Option<?>
/// - homepage: Option<?>
/// - documentation: Option<?>
/// - links: String
struct Package {
    #[allow(dead_code)]
    name: String,
    #[allow(dead_code)]
    id: String,
    #[allow(dead_code)]
    // TODO: remove?
    targets: Vec<Target>,
    dependencies: Vec<Dependency>,
    manifest_path: String,
    edition: String,
}

#[derive(Debug, Deserialize)]
/// We ignore some fields:
/// - resolve: Option<?>
/// - version: int
/// - workspace_root: String
struct Manifest {
    packages: Vec<Package>,
    #[allow(dead_code)]
    /// The workspace members are packages identified by their [id]
    workspace_members: Vec<String>,
    target_directory: String,
    metadata: Option<String>,
}

impl Display for Dependency {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(f, "      {}: kind={:?}", self.name, self.kind)
    }
}

impl Display for Target {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(
            f,
            "      {}: kind={:?}, crate_types={:?}, src_path={}",
            self.name, self.kind, self.crate_types, self.src_path
        )
    }
}

impl Display for Package {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(f, "  {}: {{\n", self.name)?;

        // id
        write!(f, "    id={};\n", self.id)?;

        // manifest_path
        write!(f, "    manifest_path={};\n", self.manifest_path)?;

        // targets
        write!(f, "    targets=[\n")?;
        for target in &self.targets {
            write!(f, "{},\n", target)?
        }
        write!(f, "    ];\n")?;

        // dependencies
        write!(f, "    dependencies=[\n")?;
        for dep in &self.dependencies {
            write!(f, "{},\n", dep)?;
        }
        write!(f, "    ];\n")?;

        write!(f, "  }}")
    }
}

impl Display for Manifest {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        // workspace_members
        write!(f, "workspace_members=[\n")?;
        for wm in &self.workspace_members {
            write!(f, "  {},\n", wm)?;
        }
        write!(f, "];\n")?;

        write!(f, "target_directory={};\n", self.target_directory)?;
        write!(f, "metadata={:?};\n", self.metadata)?;

        write!(f, "packages=[\n")?;
        for p in &self.packages {
            write!(f, "{},\n", p)?;
        }

        write!(f, "]")
    }
}

/// Small helper. See [compute_external_deps]
fn compiled_to_lib_name(remove_pre: bool, no_ext_filename: String) -> String {
    // We need to convert the filename to a vector of chars - slices of strings
    // operate over bytes, not characters
    let filename: Vec<char> = no_ext_filename.chars().collect();

    // Remove the "lib" prefix, if necessary.
    // We have to clone because borrows can't outlive the blocks in which
    // they are created, which is slightly annoying...
    let filename: Vec<char> = if remove_pre {
        let pre: Vec<char> = "lib".to_string().chars().collect();
        assert!(filename.len() > pre.len());
        assert!(&filename[0..pre.len()] == pre);
        filename[pre.len()..].to_vec()
    } else {
        filename
    };

    // Remove the hash suffix
    assert!(filename.len() > 0);
    let mut i = filename.len() - 1;
    while i > 0 {
        if filename[i] == '-' {
            return filename[0..i].iter().collect::<String>();
        }
        i -= 1;
    }
    // If we got there, it means we couldn't spot the '-' character delimiting
    // the hash suffix
    unreachable!("Invalid compiled file name: {:?}", no_ext_filename);
}

/// Small utility. See [compute_external_deps].
/// Insert [filename] in the string vector for [lib_name]. Create a new entry if
/// [lib_name] is not an entry.
///
/// There may be several compiled files for the same library (if we used different
/// versions of the compiler for instance). This is why we use a map from `String`
/// to `Vec<String>`.
fn insert_in_vec_map(map: &mut HashMap<String, Vec<String>>, lib_name: String, filename: String) {
    // There may not be an entry, in which case we initialize it - there must
    // be a better way of doing this?...
    if !(map.contains_key(&lib_name)) {
        map.insert(lib_name.clone(), Vec::new());
    }

    // Insert the new filename
    trace!("lib to compiled: {:?} -> {:?}", &lib_name, filename);
    let filenames = map.get_mut(&lib_name).unwrap();
    filenames.push(filename);
}

/// Read the manifest of a crate, find the target package and compute the external
/// dependencies.
///
/// We face the issue that we directly call the rust compiler, rather than
/// `cargo`, and thus have to give very precise arguments to our invocation
/// of rustc (more specifically: we need to provide the list of external
/// dependencies).
///
/// This is slightly annoying to do, and we place ourselves in the situation
/// where the project is built through `cargo`, and the user built the
/// (debug version) of the project *before* calling Charon. In this situation,
/// we can leverage the fact that the external dependencies have already been
/// compiled, and can be found in the target directory (`/target/debug/deps/`,
/// usually).
/// We thus don't have to build them (and don't want anyway! Charon is not a
/// build system), and just need to:
/// - use the manifest (the `Cargo.toml` file) to retrieve the list of external
///   dependencies
/// - explore the target `/target/debug/deps` directory to retrieve the names of
///   the compiled libraries, to compute the arguments with which to invoke the
///   Rust compiler
///
/// Finally, the code used in this function to read the manifest and compute
/// the list of external dependencies is greatly inspired by the code used in
/// [hacspec](https://github.com/hacspec/), so all credits to them.
fn read_manifest_compute_external_deps(source_file: &PathBuf) -> (Manifest, Package, Vec<String>) {
    use std::str::FromStr;

    // Compute the path to the crate
    // Use the source file as a starting point.
    // Remove the file name
    let source_file = std::fs::canonicalize(&source_file).unwrap();
    let crate_path = source_file.as_path().parent().unwrap().parent().unwrap();
    let mut manifest_path = crate_path.to_path_buf();
    manifest_path.push(PathBuf::from_str("Cargo.toml").unwrap());
    let manifest_path = manifest_path.to_str().unwrap().to_string();

    // First, read the manifest (comes from hacspec)
    info!("Reading manifest: {:?}", manifest_path);

    // Compute the command to apply
    let output_args = vec![
        // We want to read the metadata
        "metadata".to_string(),
        // We need the verbose version of the manifest
        "-v".to_string(),
        // Focus on the workspace members
        "--no-deps".to_string(),
        // For stability (and to prevent cargo from printing an annoying warning
        // message), select a format version
        "--format-version".to_string(),
        "1".to_string(),
        // We need to provide the path to the manifest
        "--manifest-path".to_string(),
        manifest_path.clone(),
    ];

    trace!("cargo metadata command args: {:?}", output_args);

    // Apply the command
    let output = std::process::Command::new("cargo")
        .args(output_args)
        .output()
        .expect(" ⚠️  Error reading cargo manifest.");
    let stdout = output.stdout;
    if !output.status.success() {
        let error =
            String::from_utf8(output.stderr).expect(" ⚠️  Failed reading cargo's stderr output");
        panic!("Error running cargo metadata: {:?}", error);
    }
    let json_string = String::from_utf8(stdout).expect(" ⚠️  Failed reading cargo output");
    let manifest: Manifest = serde_json::from_str(&json_string)
        .expect(" ⚠️  Error reading the manifest (Cargo.toml file) processed by cargo");

    trace!("manifest: {}", manifest);

    // The manifest lists all the packages we need to build (including the
    // dependencies' dependencies). We only want to retrieve the information
    // about the package for the local crate (assuming there is only one).
    // We thought of using the [workspace_members] field, but it actually
    // contains a lot of unrelated packages. We thus do this in a slightly
    // hacky way: we find the package whose [manifest_path] field matches
    // the current manifest.
    // Rmk: in theory, it would be cleaner if we didn't give a source file
    // as input argument to Charon, but rather a directory (from where we
    // would find the manifest, then lookup the proper target, which would
    // contain the source path indicating the entry point of the crate).
    // For now we don't do this because we want to be able to extract
    // sub-parts of a crate (by using the proper entry points): we might
    // change that in the future.

    // Find all the packages whose [manifest_path] matches the current manifest
    let mut tgt_packages: Vec<Package> = Vec::new();
    for package in &manifest.packages {
        if package.manifest_path == manifest_path {
            tgt_packages.push(package.clone());
        }
    }
    // Check that we found exactly one package
    assert!(tgt_packages.len() == 1);

    let tgt_package = tgt_packages.pop().unwrap();

    // Build systems can be annoying, especially if we use different versions
    // of the compiler (Charon relies on a nightly version, which may be
    // different from the one used by the user to compile his project! - this
    // can result in rustc considering the compiled libraries as invalid,
    // because of a version mismatch).
    // We don't want to take the user by surprise if something goes wrong,
    // so we print as much information as we can.
    // Rk.: this is a rather problematic issue, because we don't want to force
    // the user to compile his project with a specific version of the compiler.
    // We need to think of a way around (the most brutal way would be to clone
    // the project in a subdirectory, and compile it in debug mode with the
    // proper compiler - by inserting the proper `rust-toolchain` file - before
    // calling charon; this should be easy to script).

    // List the dependencies.
    // We do something simple: we list the dependencies for the target package,
    // as having useless dependencies shouldn't be a problem.
    // We make sure we don't have duplicates while doing so.
    let mut deps: HashSet<String> = HashSet::new();
    for dep in &tgt_package.dependencies {
        // We keep only the "regular" dependencies (for instance, we filter
        // the dependencies from "dev-dependencies") by keeping only the
        // dependencies with kind=None.
        if dep.kind.is_some() {
            // Sanity check: the kind should be in a specific set
            let kind = dep.kind.as_ref().unwrap();
            assert!(kind == "dev");
            continue;
        }

        // A crate name may use the "-" symbol, however this symbol gets
        // replaced with "_" at compilation: we thus need to convert it
        // before registering it.
        // Note that we need to do the conversion now, because when looking
        // in the directory file containing all the compiled dependencies,
        // we filter the useless dependencies.
        let dep = str::replace(&dep.name, "-", "_");
        deps.insert(dep);
    }
    trace!("List of external dependencies: {:?}", deps);

    // Compute the path to the compiled dependencies
    let target_dir = format!("{}/debug/deps/", &manifest.target_directory);
    let deps_dir = PathBuf::from_str(&target_dir).unwrap();
    let deps_dir = crate_path.join(deps_dir);
    info!(
        "Looking for the compiled external dependencies in: {:?}",
        deps_dir
    );

    // List the files in the dependencies
    // There are .rmeta, .rlib, .d and .so files.
    // All the files have a hash suffix.
    // The .rmeta, .rlib and .so files have a "lib" prefix.
    // Ex.:
    // - External "remote" crates:
    //   "libserde_json-25bfd2343c819291.rlib"
    // - Local crates:
    //   "attributes-b73eebf157017326.d"
    //   "libattributes-b73eebf157017326.so"
    //
    // We list all the compiled files in the target directory and retrieve the
    // original library name (i.e., "serde_json" or "attributes" in the above
    // examples), then compute a map from library name to compiled files.
    //
    // It happens that there are several compiled files for the same dependency:
    // we store them all in a vector.
    let files = std::fs::read_dir(deps_dir.clone()).unwrap();
    let mut lib_to_rmeta: HashMap<String, Vec<String>> = HashMap::new();
    let mut lib_to_rlib: HashMap<String, Vec<String>> = HashMap::new();
    let mut lib_to_so: HashMap<String, Vec<String>> = HashMap::new();
    let mut lib_to_d: HashMap<String, Vec<String>> = HashMap::new();
    for file in files {
        trace!("File: {:?}", file);
        match file {
            std::io::Result::Ok(entry) => {
                let entry = entry.path();

                // We only keep the files with .rlib or .d extension
                let extension = entry.extension();
                if extension.is_none() {
                    continue;
                }
                let extension = extension.unwrap().to_str().unwrap();
                if extension != "rmeta"
                    && extension != "rlib"
                    && extension != "so"
                    && extension != "d"
                {
                    continue;
                }
                // The file has a "lib" prefix if and only if its extension is
                // ".rmeta", ".rlib" or ".so"
                let is_rmeta = extension == "rmeta";
                let is_rlib = extension == "rlib";
                let is_so = extension == "so";
                let has_prefix = is_rmeta || is_rlib || is_so;

                // Retrieve the file name
                let filename = PathBuf::from(entry.file_name().unwrap());

                // Remove the extension
                let no_ext_filename = filename.file_stem().unwrap().to_str().unwrap().to_string();

                // Compute the library name (remove the "lib" prefix for .rlib files,
                // remove the hash suffix)
                let lib_name = compiled_to_lib_name(has_prefix, no_ext_filename);

                // Only keep the libraries for the dependencies we need
                if !(deps.contains(&lib_name)) {
                    continue;
                }

                // Insert in the proper map - note that we need the full path
                let full_path = deps_dir.join(entry).to_str().unwrap().to_string();
                if is_rmeta {
                    insert_in_vec_map(&mut lib_to_rmeta, lib_name, full_path);
                } else if is_rlib {
                    insert_in_vec_map(&mut lib_to_rlib, lib_name, full_path);
                } else if is_so {
                    insert_in_vec_map(&mut lib_to_so, lib_name, full_path);
                } else {
                    insert_in_vec_map(&mut lib_to_d, lib_name, full_path);
                }
            }
            std::io::Result::Err(_) => {
                panic!("Unexpected error while reading files in: {:?}", deps_dir);
            }
        }
    }

    // Generate the additional arguments
    let mut args: Vec<String> = Vec::new();

    // Add the "-L" dependency
    args.push("-L".to_string());
    args.push(format!("dependency={}", deps_dir.to_str().unwrap().to_string()).to_string());

    // Add the "--extern" arguments
    for dep in deps {
        // Retrieve the path to the compiled library.
        // We look in the following order:
        // - .rmeta
        // - .rlib files
        // - .so files
        let libs = [&lib_to_rmeta, &lib_to_rlib, &lib_to_so];
        let mut compiled_path = None;
        for lib in libs {
            compiled_path = lib.get(&dep);
            if compiled_path.is_some() {
                break;
            }
        }
        if compiled_path.is_none() {
            error!(
                "Could not find a compiled file for the external dependency {:?} in {:?}. You may need to build the crate: `cargo build`.",
                dep, deps_dir
            );
            panic!();
        }

        if compiled_path.is_none() {
            error!(
                "Could not find a compiled file for the external dependency {:?} in {:?}. You may need to build the crate: `cargo build`.",
                dep, deps_dir
            );
            panic!();
        }

        // Check that there is exactly one compiled library
        let compiled_path = compiled_path.unwrap();
        assert!(compiled_path.len() > 0);
        if compiled_path.len() > 1 {
            error!("Found two compiled library files for the same external dependency ({:?}): {:?}, {:?}. You may want to clean the target directory (`rm \"{:?}/*\"`) then rebuild the project with `cargo build`",
                    dep, &compiled_path[0], &compiled_path[1], deps_dir);
            panic!();
        }

        args.push("--extern".to_string());
        args.push(format!("{}={}", dep, &compiled_path[0]).to_string());
    }

    // Return
    trace!("Args vec: {:?}", args);
    (manifest, tgt_package, args)
}

fn main() {
    // Initialize the logger
    initialize_logger();

    // Retrieve the executable path - this is not considered an argument,
    // and won't be parsed by CliOpts
    let exec_path = match std::env::args().next() {
        Some(s) => s.to_owned(),
        None => panic!("Impossible: zero arguments on the command-line!"),
    };

    // Parse the command-line
    let args = CliOpts::from_args();

    // Retrieve the sysroot (the path to the executable of the compiler)
    let out = std::process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = std::str::from_utf8(&out.stdout).unwrap().trim();
    let sysroot_arg = format!("--sysroot={}", sysroot).to_owned();

    // Read the manifest, find the target package and compute the list of external
    // dependencies.
    let (_manifest, package, mut external_deps) =
        read_manifest_compute_external_deps(&args.input_file);

    // Call the Rust compiler with the proper options
    let mut compiler_args = vec![
        exec_path,
        sysroot_arg,
        args.input_file.as_path().to_str().unwrap().to_string(),
        "--crate-type=lib".to_string(),
        format!("--edition={}", package.edition).to_string(),
    ];
    if args.use_polonius {
        compiler_args.push("-Zpolonius".to_string());
    }
    compiler_args.append(&mut external_deps);

    trace!("Compiler args: {:?}", compiler_args.join(" "));

    // When calling the compiler we provide a callback, which allows us
    // to retrieve the result of compiler queries
    RunCompiler::new(
        &compiler_args,
        &mut ToInternal {
            dest_dir: args.dest_dir,
            source_file: args.input_file,
            no_code_duplication: args.no_code_duplication,
            opaque_modules: args.opaque,
        },
    )
    .run()
    .unwrap();
}

/// Translate a crate to LLBC (Low-Level Borrow Calculus).
///
/// This function is a callback function for the Rust compiler.
fn translate(sess: &Session, tcx: TyCtxt, internal: &ToInternal) -> Result<(), ()> {
    trace!();
    // Retrieve the crate name.
    let crate_name = tcx
        .crate_name(rustc_span::def_id::LOCAL_CRATE)
        .to_ident_string();
    trace!("# Crate: {}", crate_name);

    // Some important notes about crates and how to interact with rustc:
    // - when calling rustc, we should give it the root of the crate, for
    //   instance the "main.rs" file. From there, rustc will load all the
    //   *modules* (i.e., files) in the crate
    // - whenever there is a `mod MODULE` in a file (for instance, in the
    //   "main.rs" file), it becomes a Module HIR item

    // # Step 1: check and register all the definitions, to build the graph
    // of dependencies between them (we need to know in which
    // order to extract the definitions, and which ones are mutually
    // recursive). While building this graph, we perform as many checks as
    // we can to make sure the code is in the proper rust subset. Those very
    // early steps mostly involve checking whether some features are used or
    // not (ex.: raw pointers, inline ASM, etc.). More complex checks are
    // performed later. In general, whenever there is ambiguity on the potential
    // step in which a step could be performed, we perform it as soon as possible.
    // Building the graph of dependencies allows us to translate the definitions
    // in the proper order, and to figure out which definitions are mutually
    // recursive.
    // We iterate over the HIR items, and explore their MIR bodies/ADTs/etc.
    // (when those exist - for instance, type aliases don't have MIR translations
    // so we just ignore them).
    let crate_info = register::CrateInfo {
        crate_name: crate_name.clone(),
        opaque_mods: HashSet::from_iter(internal.opaque_modules.clone().into_iter()),
    };
    let registered_decls = register::register_crate(&crate_info, sess, tcx)?;

    // # Step 2: reorder the graph of dependencies and compute the strictly
    // connex components to:
    // - compute the order in which to extract the definitions
    // - find the recursive definitions
    // - group the mutually recursive definitions
    let ordered_decls = reorder_decls::reorder_declarations(&registered_decls)?;

    // # Step 3: generate identifiers for the types and functions, and compute
    // the mappings from rustc identifiers to our own identifiers
    let ordered_decls = rust_to_local_ids::rust_to_local_ids(&ordered_decls);

    // # Step 4: translate the types
    let (types_constraints, type_defs) = translate_types::translate_types(tcx, &ordered_decls)?;

    // # Step 5: translate the functions to IM (our Internal representation of MIR).
    // Note that from now onwards, both type and function definitions have been
    // translated to our internal ASTs: we don't interact with rustc anymore.
    let (im_fun_defs, im_global_defs) = translate_functions_to_im::translate_functions(
        tcx,
        &ordered_decls,
        &types_constraints,
        &type_defs,
    )?;

    // # Step 6: go from IM to LLBC (Low-Level Borrow Calculus) by reconstructing
    // the control flow.
    let (mut llbc_funs, mut llbc_globals) = im_to_llbc::translate_functions(
        internal.no_code_duplication,
        &type_defs,
        &im_fun_defs,
        &im_global_defs,
    );

    //
    // =================
    // **Micro-passes**:
    // =================
    // At this point, the bulk of the translation is done. From now onwards,
    // we simply apply some micro-passes to make the code cleaner, before
    // serializing the result.
    //

    // # Step 7: simplify the calls to unops and binops
    // Note that we assume that the sequences have been flattened.
    simplify_ops::simplify(&mut llbc_funs, &mut llbc_globals);

    // # Step 8: replace constant (OperandConstantValue) ADTs by regular (Aggregated) ADTs.
    regularize_constant_adts::transform(&mut llbc_funs, &mut llbc_globals);

    // # Step 9: extract statics and constant globals from operands (put them in
    // a let binding). This pass relies on the absence of constant ADTs from
    // the previous step: it does not inspect them (so it would miss globals in
    // constant ADTs).
    extract_global_assignments::transform(&mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After binop simplification:\n{}\n",
            def.fmt_with_defs(&type_defs, &llbc_funs, &llbc_globals)
        );
    }

    // # Step 10: reconstruct the asserts
    reconstruct_asserts::simplify(&mut llbc_funs, &mut llbc_globals);

    for def in &llbc_funs {
        trace!(
            "# After asserts reconstruction:\n{}\n",
            def.fmt_with_defs(&type_defs, &llbc_funs, &llbc_globals)
        );
    }

    // # Step 11: add the missing assignments to the return value.
    // When the function return type is unit, the generated MIR doesn't
    // set the return value to `()`. This can be a concern: in the case
    // of Aeneas, it means the return variable contains ⊥ upon returning.
    // For this reason, when the function has return type unit, we insert
    // an extra assignment just before returning.
    // This also applies to globals (for checking or executing code before
    // the main or at compile-time).
    insert_assign_return_unit::transform(&mut llbc_funs, &mut llbc_globals);

    // # Step 12: remove the locals which are never used. After doing so, we
    // check that there are no remaining locals with type `Never`.
    remove_unused_locals::transform(&mut llbc_funs, &mut llbc_globals);

    // # Step 13: compute which functions are potentially divergent. A function
    // is potentially divergent if it is recursive, contains a loop or transitively
    // calls a potentially divergent function.
    // Note that in the future, we may complement this basic analysis with a
    // finer analysis to detect recursive functions which are actually total
    // by construction.
    // Because we don't have loops, constants are not yet touched.
    let _divergent = divergent::compute_divergent_functions(&ordered_decls, &llbc_funs);

    // # Step 14: generate the files.
    llbc_export::export(
        crate_name,
        &ordered_decls,
        &type_defs,
        &llbc_funs,
        &llbc_globals,
        &internal.dest_dir,
        &internal.source_file,
    )?;

    trace!("Done");

    Ok(())
}
