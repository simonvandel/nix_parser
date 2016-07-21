extern crate nix_parser;
extern crate clap;

use clap::*;
use nix_parser::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;

fn main() {
    let matches = App::new("nix_parser example ast printer")
        .version("0.1.0")
        .author("Simon Vandel Sillesen <simon.vandel@gmail.com>")
        .about("Demonstrates this Nix parser.")
/*        .args_from_usage(
            "<INPUT>             'Sets the input Nix file to parse'")*/
        .arg(Arg::with_name("INPUT")
            .required(true)
            .help("Sets the input Nix file to parse")
            .validator(|input_file_path| {
                if input_file_path.ends_with(".nix") {Ok(())}
                else {Err("Specified file is not ending in '.nix', so I refuse to parse it.".to_string())}
            }))
        .get_matches();

    // It is okay to unwrap this, as it is a required argument
    let input_file_path = matches.value_of("INPUT").map(Path::new).unwrap();
    let mut input_file_content = Vec::new();

    let res = File::open(&input_file_path)
        .and_then(|mut file| file.read_to_end(&mut input_file_content))
        .map(|_| {
            match nix_expr(input_file_content.as_slice()) {
                // TODO: The clone is ugly, fix it
                IResult::Done(x, ref output) if x.is_empty() => output.clone(),
                IResult::Done(not_consumed, _) =>
                    panic!("Reached Done, but did not consume the whole input file. Not consumed: {:?}", not_consumed),
                IResult::Incomplete(rest) => panic!("Incomplete with rest: {:?}", rest),
                IResult::Error(err) => panic!("Incomplete with rest: {:?}", err)
            }
        })
        .map(|nix_expr| pretty_format(&nix_expr));

    println!("{:?}", res);
}

fn pretty_format(expr: &NixExpr) -> String {
    let pretty_str = match *expr {
        NixExpr::Assert(_, _) => "assert",
        _ => "asdad"
    };

    pretty_str.to_string()
}