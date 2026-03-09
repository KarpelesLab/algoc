//! AlgoC CLI - Algorithm pseudocode transpiler

use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use algoc::parser::{Ast, Item, ItemKind};
use algoc::{CodeGenerator, Parser, analyze, errors::print_error};

/// Create a code generator for the given target name
fn create_generator(target: &str, include_tests: bool) -> Option<Box<dyn CodeGenerator>> {
    match target {
        "javascript" | "js" => Some(Box::new(
            algoc::JavaScriptGenerator::new().with_tests(include_tests),
        )),
        "python" | "py" => Some(Box::new(
            algoc::PythonGenerator::new().with_tests(include_tests),
        )),
        "rust" | "rs" => Some(Box::new(
            algoc::RustGenerator::new().with_tests(include_tests),
        )),
        "c" => Some(Box::new(algoc::CGenerator::new().with_tests(include_tests))),
        "cpp" | "c++" | "cxx" => Some(Box::new(
            algoc::CppGenerator::new().with_tests(include_tests),
        )),
        "go" | "golang" => Some(Box::new(
            algoc::GoGenerator::new().with_tests(include_tests),
        )),
        "java" => Some(Box::new(
            algoc::JavaGenerator::new().with_tests(include_tests),
        )),
        "kotlin" | "kt" => Some(Box::new(
            algoc::KotlinGenerator::new().with_tests(include_tests),
        )),
        "swift" => Some(Box::new(
            algoc::SwiftGenerator::new().with_tests(include_tests),
        )),
        "dart" => Some(Box::new(
            algoc::DartGenerator::new().with_tests(include_tests),
        )),
        "php" => Some(Box::new(
            algoc::PhpGenerator::new().with_tests(include_tests),
        )),
        "perl" | "pl" => Some(Box::new(
            algoc::PerlGenerator::new().with_tests(include_tests),
        )),
        "objc" | "objective-c" | "objectivec" => Some(Box::new(
            algoc::ObjCGenerator::new().with_tests(include_tests),
        )),
        "vhdl" => Some(Box::new(
            algoc::VhdlGenerator::new().with_tests(include_tests),
        )),
        "verilog" | "v" => Some(Box::new(
            algoc::VerilogGenerator::new().with_tests(include_tests),
        )),
        _ => None,
    }
}

const AVAILABLE_TARGETS: &str = "javascript (js), python (py), rust (rs), c, c++ (cpp), go, java, kotlin (kt), swift, dart, php, perl (pl), objc, vhdl, verilog (v)";

/// Load and parse a file, recursively processing `use` statements
fn load_with_imports(
    filepath: &Path,
    loaded: &mut HashSet<PathBuf>,
) -> Result<Ast, (String, String)> {
    // Canonicalize to detect circular/duplicate imports
    let canonical = filepath.canonicalize().map_err(|e| {
        (
            filepath.display().to_string(),
            format!("cannot resolve path: {}", e),
        )
    })?;

    // Skip if already loaded
    if loaded.contains(&canonical) {
        return Ok(Ast { items: Vec::new() });
    }
    loaded.insert(canonical.clone());

    // Read source
    let source = fs::read_to_string(filepath).map_err(|e| {
        (
            filepath.display().to_string(),
            format!("cannot read file: {}", e),
        )
    })?;

    // Parse
    let parser = Parser::new(&source);
    let ast = parser
        .parse()
        .map_err(|e| (filepath.display().to_string(), format!("{}", e)))?;

    // Process imports and collect items
    let mut all_items: Vec<Item> = Vec::new();
    let base_dir = filepath.parent().unwrap_or(Path::new("."));

    for item in ast.items {
        if let ItemKind::Use(ref use_def) = item.kind {
            // Resolve relative path
            let import_path = base_dir.join(&use_def.path);

            // Recursively load
            let imported_ast = load_with_imports(&import_path, loaded)?;
            all_items.extend(imported_ast.items);
        } else {
            all_items.push(item);
        }
    }

    Ok(Ast { items: all_items })
}

/// Load a file with all its imports resolved
fn load_file(filename: &str) -> Result<(Ast, String), (String, String)> {
    let path = Path::new(filename);
    let mut loaded = HashSet::new();

    // Read the source for error reporting
    let source = fs::read_to_string(path)
        .map_err(|e| (filename.to_string(), format!("cannot read file: {}", e)))?;

    let ast = load_with_imports(path, &mut loaded)?;
    Ok((ast, source))
}

/// Run a test for an interpreted target
fn run_interpreted_test(code: &str, interpreter: &str, flag: &str, suffix: &str) -> ExitCode {
    let code_with_runner = format!("{}{}", code, suffix);
    let status = Command::new(interpreter)
        .arg(flag)
        .arg(&code_with_runner)
        .status();
    match status {
        Ok(s) if s.success() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("Error running {}: {}", interpreter, e);
            ExitCode::FAILURE
        }
    }
}

/// Run a test for a compiled target
fn run_compiled_test(code: &str, ext: &str, target: &str) -> ExitCode {
    let temp_dir = env::temp_dir();
    let source_path = temp_dir.join(format!("algoc_run.{}", ext));
    let binary_path = temp_dir.join("algoc_test_bin");

    // Write source file
    if let Err(e) = fs::write(&source_path, code) {
        eprintln!("Error writing temp file: {}", e);
        return ExitCode::FAILURE;
    }

    let result = match target {
        "rust" | "rs" => {
            let compile = Command::new("rustc")
                .arg(&source_path)
                .arg("-o")
                .arg(&binary_path)
                .status();
            match compile {
                Ok(s) if s.success() => Command::new(&binary_path).status(),
                Ok(s) => {
                    let _ = fs::remove_file(&source_path);
                    return if s.success() {
                        ExitCode::SUCCESS
                    } else {
                        ExitCode::FAILURE
                    };
                }
                Err(e) => {
                    eprintln!("Error running rustc: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            }
        }
        "c" => {
            let compile = Command::new("gcc")
                .args(["-std=c11", "-O2", "-lm", "-o"])
                .arg(&binary_path)
                .arg(&source_path)
                .status();
            match compile {
                Ok(s) if s.success() => Command::new(&binary_path).status(),
                Ok(_) => {
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running gcc: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            }
        }
        "cpp" | "c++" | "cxx" => {
            let compile = Command::new("g++")
                .args(["-std=c++20", "-O2", "-o"])
                .arg(&binary_path)
                .arg(&source_path)
                .status();
            match compile {
                Ok(s) if s.success() => Command::new(&binary_path).status(),
                Ok(_) => {
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running g++: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            }
        }
        "go" | "golang" => {
            let status = Command::new("go").arg("run").arg(&source_path).status();
            let _ = fs::remove_file(&source_path);
            return match status {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running go: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        "java" => {
            // Java needs the class name to match the file name
            let java_path = temp_dir.join("AlgocTest.java");
            let _ = fs::write(&java_path, code);
            let compile = Command::new("javac").arg(&java_path).status();
            let result = match compile {
                Ok(s) if s.success() => Command::new("java")
                    .arg("-cp")
                    .arg(&temp_dir)
                    .arg("AlgocTest")
                    .status(),
                Ok(_) => {
                    let _ = fs::remove_file(&java_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running javac: {}", e);
                    let _ = fs::remove_file(&java_path);
                    return ExitCode::FAILURE;
                }
            };
            let _ = fs::remove_file(&java_path);
            let _ = fs::remove_file(temp_dir.join("AlgocTest.class"));
            return match result {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running java: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        "kotlin" | "kt" => {
            let jar_path = temp_dir.join("algoc_test.jar");
            let compile = Command::new("kotlinc")
                .arg(&source_path)
                .args(["-include-runtime", "-d"])
                .arg(&jar_path)
                .status();
            let result = match compile {
                Ok(s) if s.success() => Command::new("java").arg("-jar").arg(&jar_path).status(),
                Ok(_) => {
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running kotlinc: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            };
            let _ = fs::remove_file(&source_path);
            let _ = fs::remove_file(&jar_path);
            return match result {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running java: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        "swift" => {
            let binary_path = source_path.with_extension("");
            let compile = Command::new("swiftc")
                .arg("-Onone")
                .arg("-o")
                .arg(&binary_path)
                .arg(&source_path)
                .status();
            let _ = fs::remove_file(&source_path);
            match compile {
                Ok(s) if s.success() => {
                    let status = Command::new(&binary_path).status();
                    let _ = fs::remove_file(&binary_path);
                    return match status {
                        Ok(s) if s.success() => ExitCode::SUCCESS,
                        Ok(_) => ExitCode::FAILURE,
                        Err(e) => {
                            eprintln!("Error running swift binary: {}", e);
                            ExitCode::FAILURE
                        }
                    };
                }
                Ok(_) => {
                    let _ = fs::remove_file(&binary_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error compiling swift: {}", e);
                    return ExitCode::FAILURE;
                }
            }
        }
        "dart" => {
            let status = Command::new("dart").arg("run").arg(&source_path).status();
            let _ = fs::remove_file(&source_path);
            return match status {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running dart: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        "objc" | "objective-c" | "objectivec" => {
            let compile = Command::new("gcc")
                .args(["-O2", "-lobjc", "-o"])
                .arg(&binary_path)
                .arg(&source_path)
                .status();
            match compile {
                Ok(s) if s.success() => Command::new(&binary_path).status(),
                Ok(_) => {
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running gcc: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            }
        }
        "verilog" | "v" => {
            let vvp_path = temp_dir.join("algoc_test.vvp");
            let compile = Command::new("iverilog")
                .arg("-o")
                .arg(&vvp_path)
                .arg(&source_path)
                .status();
            let result = match compile {
                Ok(s) if s.success() => Command::new("vvp").arg(&vvp_path).status(),
                Ok(_) => {
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("Error running iverilog: {}", e);
                    let _ = fs::remove_file(&source_path);
                    return ExitCode::FAILURE;
                }
            };
            let _ = fs::remove_file(&source_path);
            let _ = fs::remove_file(&vvp_path);
            return match result {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running vvp: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        "vhdl" => {
            let work_dir = temp_dir.join("algoc_vhdl_work");
            let _ = fs::create_dir_all(&work_dir);
            let analyze = Command::new("ghdl")
                .arg("-a")
                .arg(format!("--workdir={}", work_dir.display()))
                .arg(&source_path)
                .status();
            let result = match analyze {
                Ok(s) if s.success() => {
                    let elab = Command::new("ghdl")
                        .arg("-e")
                        .arg(format!("--workdir={}", work_dir.display()))
                        .arg("testbench")
                        .status();
                    match elab {
                        Ok(s) if s.success() => Command::new("ghdl")
                            .arg("-r")
                            .arg(format!("--workdir={}", work_dir.display()))
                            .arg("testbench")
                            .status(),
                        other => other,
                    }
                }
                other => other,
            };
            let _ = fs::remove_file(&source_path);
            let _ = fs::remove_dir_all(&work_dir);
            return match result {
                Ok(s) if s.success() => ExitCode::SUCCESS,
                Ok(_) => ExitCode::FAILURE,
                Err(e) => {
                    eprintln!("Error running ghdl: {}", e);
                    ExitCode::FAILURE
                }
            };
        }
        _ => {
            eprintln!("No test runner for target: {}", target);
            let _ = fs::remove_file(&source_path);
            return ExitCode::FAILURE;
        }
    };

    // Common cleanup for compile-then-run targets
    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_file(&binary_path);
    match result {
        Ok(s) if s.success() => ExitCode::SUCCESS,
        Ok(_) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("Error running test binary: {}", e);
            ExitCode::FAILURE
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("AlgoC - Algorithm Pseudocode Transpiler");
        println!("Version {}", env!("CARGO_PKG_VERSION"));
        println!();
        println!("Usage: algoc <command> [options]");
        println!();
        println!("Commands:");
        println!("  check <file>           Type-check a source file");
        println!("  parse <file>           Parse and dump AST (no type checking)");
        println!("  compile <file> -t <target> [-o <output>] [--test]");
        println!("                         Compile to target language");
        println!("  test <file> [-t <target>]");
        println!("                         Run tests directly");
        println!();
        println!("Targets: {}", AVAILABLE_TARGETS);
        println!();
        return ExitCode::SUCCESS;
    }

    let command = &args[1];

    match command.as_str() {
        "parse" => {
            if args.len() < 3 {
                eprintln!("Error: missing file argument");
                return ExitCode::FAILURE;
            }

            let filename = &args[2];
            let source = match fs::read_to_string(filename) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error reading file '{}': {}", filename, e);
                    return ExitCode::FAILURE;
                }
            };

            let parser = Parser::new(&source);
            match parser.parse() {
                Ok(ast) => {
                    println!("Parsed {} items:", ast.items.len());
                    for item in &ast.items {
                        match &item.kind {
                            algoc::parser::ItemKind::Function(f) => {
                                println!("  fn {} ({} params)", f.name.name, f.params.len());
                            }
                            algoc::parser::ItemKind::Struct(s) => {
                                println!("  struct {} ({} fields)", s.name.name, s.fields.len());
                            }
                            algoc::parser::ItemKind::Layout(l) => {
                                println!("  layout {} ({} fields)", l.name.name, l.fields.len());
                            }
                            algoc::parser::ItemKind::Const(c) => {
                                println!("  const {}", c.name.name);
                            }
                            algoc::parser::ItemKind::Test(t) => {
                                println!(
                                    "  test {} ({} statements)",
                                    t.name.name,
                                    t.body.stmts.len()
                                );
                            }
                            algoc::parser::ItemKind::Use(u) => {
                                println!("  use \"{}\"", u.path);
                            }
                            algoc::parser::ItemKind::Enum(e) => {
                                println!("  enum {} ({} variants)", e.name.name, e.variants.len());
                            }
                            algoc::parser::ItemKind::Impl(i) => {
                                println!("  impl {} ({} methods)", i.target.name, i.methods.len());
                            }
                            algoc::parser::ItemKind::Interface(i) => {
                                println!(
                                    "  interface {} ({} methods)",
                                    i.name.name,
                                    i.methods.len()
                                );
                            }
                        }
                    }
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_error(&source, filename, &e);
                    ExitCode::FAILURE
                }
            }
        }
        "check" => {
            if args.len() < 3 {
                eprintln!("Error: missing file argument");
                return ExitCode::FAILURE;
            }

            let filename = &args[2];

            // Load file with imports
            let (ast, source) = match load_file(filename) {
                Ok((ast, source)) => (ast, source),
                Err((file, msg)) => {
                    eprintln!("Error in '{}': {}", file, msg);
                    return ExitCode::FAILURE;
                }
            };

            // Analyze (name resolution + type checking)
            match analyze(ast) {
                Ok(analyzed) => {
                    println!(
                        "OK: {} items type-checked successfully",
                        analyzed.ast.items.len()
                    );

                    // Print some analysis info
                    let symbols: Vec<_> = analyzed.global_scope.symbols().collect();
                    let structs: Vec<_> = analyzed.global_scope.structs().collect();

                    if !symbols.is_empty() {
                        println!("\nSymbols:");
                        for (name, sym) in symbols {
                            println!("  {}: {}", name, sym.ty);
                        }
                    }

                    if !structs.is_empty() {
                        println!("\nStructs:");
                        for (name, def) in structs {
                            println!("  {} ({} fields)", name, def.fields.len());
                        }
                    }

                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_error(&source, filename, &e);
                    ExitCode::FAILURE
                }
            }
        }
        "compile" => {
            if args.len() < 3 {
                eprintln!("Error: missing file argument");
                return ExitCode::FAILURE;
            }

            let filename = &args[2];

            // Parse arguments
            let mut target = None;
            let mut output = None;
            let mut include_tests = false;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "-t" | "--target" => {
                        if i + 1 < args.len() {
                            target = Some(args[i + 1].clone());
                            i += 2;
                        } else {
                            eprintln!("Error: -t requires a target");
                            return ExitCode::FAILURE;
                        }
                    }
                    "-o" | "--output" => {
                        if i + 1 < args.len() {
                            output = Some(args[i + 1].clone());
                            i += 2;
                        } else {
                            eprintln!("Error: -o requires an output path");
                            return ExitCode::FAILURE;
                        }
                    }
                    "--test" => {
                        include_tests = true;
                        i += 1;
                    }
                    _ => {
                        eprintln!("Unknown option: {}", args[i]);
                        return ExitCode::FAILURE;
                    }
                }
            }

            let target = match target {
                Some(t) => t,
                None => {
                    eprintln!("Error: -t <target> is required");
                    eprintln!("Available targets: {}", AVAILABLE_TARGETS);
                    return ExitCode::FAILURE;
                }
            };

            // Load file with imports
            let (ast, source) = match load_file(filename) {
                Ok((ast, source)) => (ast, source),
                Err((file, msg)) => {
                    eprintln!("Error in '{}': {}", file, msg);
                    return ExitCode::FAILURE;
                }
            };

            // Analyze
            let analyzed = match analyze(ast) {
                Ok(a) => a,
                Err(e) => {
                    print_error(&source, filename, &e);
                    return ExitCode::FAILURE;
                }
            };

            // Create generator
            let mut generator = match create_generator(&target, include_tests) {
                Some(g) => g,
                None => {
                    eprintln!("Unknown target: {}", target);
                    eprintln!("Available targets: {}", AVAILABLE_TARGETS);
                    return ExitCode::FAILURE;
                }
            };

            // Generate code
            let code = match generator.generate(&analyzed) {
                Ok(code) => code,
                Err(e) => {
                    print_error(&source, filename, &e);
                    return ExitCode::FAILURE;
                }
            };

            // Write output
            let output_path = output.unwrap_or_else(|| {
                let stem = std::path::Path::new(filename)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("output");
                format!("{}.{}", stem, generator.file_extension())
            });

            match fs::write(&output_path, &code) {
                Ok(_) => {
                    println!("Generated: {} ({} bytes)", output_path, code.len());
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    eprintln!("Error writing '{}': {}", output_path, e);
                    ExitCode::FAILURE
                }
            }
        }
        "test" => {
            if args.len() < 3 {
                eprintln!("Error: missing file argument");
                return ExitCode::FAILURE;
            }

            let filename = &args[2];

            // Parse arguments
            let mut target = String::from("js"); // Default to JavaScript
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "-t" | "--target" => {
                        if i + 1 < args.len() {
                            target = args[i + 1].clone();
                            i += 2;
                        } else {
                            eprintln!("Error: -t requires a target");
                            return ExitCode::FAILURE;
                        }
                    }
                    _ => {
                        eprintln!("Unknown option: {}", args[i]);
                        return ExitCode::FAILURE;
                    }
                }
            }

            // Load file with imports
            let (ast, source) = match load_file(filename) {
                Ok((ast, source)) => (ast, source),
                Err((file, msg)) => {
                    eprintln!("Error in '{}': {}", file, msg);
                    return ExitCode::FAILURE;
                }
            };

            // Analyze
            let analyzed = match analyze(ast) {
                Ok(a) => a,
                Err(e) => {
                    print_error(&source, filename, &e);
                    return ExitCode::FAILURE;
                }
            };

            // Create generator with tests enabled
            let mut generator = match create_generator(&target, true) {
                Some(g) => g,
                None => {
                    eprintln!("Unknown target: {}", target);
                    eprintln!("Available targets: {}", AVAILABLE_TARGETS);
                    return ExitCode::FAILURE;
                }
            };

            let code = match generator.generate(&analyzed) {
                Ok(code) => code,
                Err(e) => {
                    print_error(&source, filename, &e);
                    return ExitCode::FAILURE;
                }
            };

            let ext = generator.file_extension();

            // Run test based on target type
            match target.as_str() {
                // Interpreted targets
                "javascript" | "js" => {
                    let code_with_runner = format!("{}\nprocess.exit(run_tests() ? 0 : 1);", code);
                    run_interpreted_test(&code_with_runner, "node", "-e", "")
                }
                "python" | "py" => {
                    let code_with_runner =
                        format!("{}\nimport sys; sys.exit(0 if run_tests() else 1)", code);
                    run_interpreted_test(&code_with_runner, "python3", "-c", "")
                }
                "php" => run_interpreted_test(&code, "php", "-r", ""),
                "perl" | "pl" => run_interpreted_test(&code, "perl", "-e", ""),
                // Compiled/run targets
                _ => run_compiled_test(&code, ext, &target),
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
            eprintln!("Run 'algoc' without arguments for usage information");
            ExitCode::FAILURE
        }
    }
}
