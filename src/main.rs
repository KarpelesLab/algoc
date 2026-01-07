//! AlgoC CLI - Algorithm pseudocode transpiler

use std::env;
use std::fs;
use std::process::ExitCode;

use algoc::{Parser, analyze, errors::print_error, CodeGenerator, JavaScriptGenerator};

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
        println!("  compile <file> -t <target> [-o <output>]");
        println!("                         Compile to target language");
        println!();
        println!("Targets: javascript (js)");
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
                                println!("  test {} ({} cases)", t.name.name, t.cases.len());
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
            let source = match fs::read_to_string(filename) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error reading file '{}': {}", filename, e);
                    return ExitCode::FAILURE;
                }
            };

            // Parse
            let parser = Parser::new(&source);
            let ast = match parser.parse() {
                Ok(ast) => ast,
                Err(e) => {
                    print_error(&source, filename, &e);
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
                    eprintln!("Available targets: javascript (js)");
                    return ExitCode::FAILURE;
                }
            };

            let source = match fs::read_to_string(filename) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("Error reading file '{}': {}", filename, e);
                    return ExitCode::FAILURE;
                }
            };

            // Parse
            let parser = Parser::new(&source);
            let ast = match parser.parse() {
                Ok(ast) => ast,
                Err(e) => {
                    print_error(&source, filename, &e);
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
                    let mut generator = JavaScriptGenerator::new();
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
                    eprintln!("Available targets: javascript (js)");
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
        _ => {
            eprintln!("Unknown command: {}", command);
            eprintln!("Run 'algoc' without arguments for usage information");
            ExitCode::FAILURE
        }
    }
}
