//! AlgoC CLI - Algorithm pseudocode transpiler

use std::env;
use std::fs;
use std::process::ExitCode;

use algoc::{Parser, errors::print_error};

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("AlgoC - Algorithm Pseudocode Transpiler");
        println!("Version {}", env!("CARGO_PKG_VERSION"));
        println!();
        println!("Usage: algoc <command> [options]");
        println!();
        println!("Commands:");
        println!("  check <file>     Type-check a source file");
        println!("  parse <file>     Parse and dump AST");
        println!();
        return ExitCode::SUCCESS;
    }

    let command = &args[1];

    match command.as_str() {
        "check" | "parse" => {
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
                    if command == "parse" {
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
                    } else {
                        println!("OK: {} items parsed successfully", ast.items.len());
                    }
                    ExitCode::SUCCESS
                }
                Err(e) => {
                    print_error(&source, filename, &e);
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
