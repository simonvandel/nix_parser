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

    let _ = File::open(&input_file_path)
        .and_then(|mut file| file.read_to_end(&mut input_file_content))
        .map(|_|println!("{:?}", nix_expr(input_file_content.as_slice())));
}