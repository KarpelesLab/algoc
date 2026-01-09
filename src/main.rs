//! AlgoC CLI - Algorithm pseudocode transpiler

use std::collections::HashSet;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use algoc::{Parser, analyze, errors::print_error, CodeGenerator, JavaScriptGenerator, PythonGenerator};
use algoc::parser::{Ast, Item, ItemKind};

/// Load and parse a file, recursively processing `use` statements
fn load_with_imports(
    filepath: &Path,
    loaded: &mut HashSet<PathBuf>,
) -> Result<Ast, (String, String)> {
    // Canonicalize to detect circular/duplicate imports
    let canonical = filepath.canonicalize()
        .map_err(|e| (filepath.display().to_string(), format!("cannot resolve path: {}", e)))?;

    // Skip if already loaded
    if loaded.contains(&canonical) {
        return Ok(Ast { items: Vec::new() });
    }
    loaded.insert(canonical.clone());

    // Read source
    let source = fs::read_to_string(filepath)
        .map_err(|e| (filepath.display().to_string(), format!("cannot read file: {}", e)))?;

    // Parse
    let parser = Parser::new(&source);
    let ast = parser.parse()
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
        println!("                         Run tests directly (streams to interpreter)");
        println!();
        println!("Targets: javascript (js, default), python (py)");
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
                                println!("  test {} ({} statements)", t.name.name, t.body.stmts.len());
                            }
                            algoc::parser::ItemKind::Use(u) => {
                                println!("  use \"{}\"", u.path);
                            }
                            algoc::parser::ItemKind::Enum(e) => {
                                println!("  enum {} ({} variants)", e.name.name, e.variants.len());
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
                    println!("OK: {} items type-checked successfully", analyzed.ast.items.len());

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
                    eprintln!("Available targets: javascript (js), python (py)");
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

            // Generate code
            let (code, ext) = match target.as_str() {
                "javascript" | "js" => {
                    let mut generator = JavaScriptGenerator::new().with_tests(include_tests);
                    match generator.generate(&analyzed) {
                        Ok(code) => (code, generator.file_extension()),
                        Err(e) => {
                            print_error(&source, filename, &e);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                "python" | "py" => {
                    let mut generator = PythonGenerator::new().with_tests(include_tests);
                    match generator.generate(&analyzed) {
                        Ok(code) => (code, generator.file_extension()),
                        Err(e) => {
                            print_error(&source, filename, &e);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                _ => {
                    eprintln!("Unknown target: {}", target);
                    eprintln!("Available targets: javascript (js), python (py)");
                    return ExitCode::FAILURE;
                }
            };

            // Write output
            let output_path = output.unwrap_or_else(|| {
                let stem = std::path::Path::new(filename)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("output");
                format!("{}.{}", stem, ext)
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
            let mut target = String::from("js");  // Default to JavaScript
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

            // Generate code with tests enabled
            let (code, interpreter) = match target.as_str() {
                "javascript" | "js" => {
                    let mut generator = JavaScriptGenerator::new().with_tests(true);
                    match generator.generate(&analyzed) {
                        Ok(code) => (code, "node"),
                        Err(e) => {
                            print_error(&source, filename, &e);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                "python" | "py" => {
                    let mut generator = PythonGenerator::new().with_tests(true);
                    match generator.generate(&analyzed) {
                        Ok(code) => (code, "python3"),
                        Err(e) => {
                            print_error(&source, filename, &e);
                            return ExitCode::FAILURE;
                        }
                    }
                }
                _ => {
                    eprintln!("Unknown target: {}", target);
                    eprintln!("Available targets: javascript (js), python (py)");
                    return ExitCode::FAILURE;
                }
            };

            // Append direct test execution (needed when running via -e/-c)
            let code_with_runner = if interpreter == "node" {
                format!("{}\nprocess.exit(run_tests() ? 0 : 1);", code)
            } else {
                format!("{}\nimport sys; sys.exit(0 if run_tests() else 1)", code)
            };

            // Spawn interpreter with code via -e flag (node) or -c flag (python)
            let status = if interpreter == "node" {
                Command::new(interpreter)
                    .arg("-e")
                    .arg(&code_with_runner)
                    .status()
            } else {
                Command::new(interpreter)
                    .arg("-c")
                    .arg(&code_with_runner)
                    .status()
            };

            match status {
                Ok(status) => {
                    if status.success() {
                        ExitCode::SUCCESS
                    } else {
                        ExitCode::FAILURE
                    }
                }
                Err(e) => {
                    eprintln!("Error running {}: {}", interpreter, e);
                    ExitCode::FAILURE
                }
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
            eprintln!("Run 'algoc' without arguments for usage information");
            ExitCode::FAILURE
        }
    }
}
