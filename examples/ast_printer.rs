extern crate nix_parser;
extern crate clap;
#[macro_use] extern crate itertools;

use clap::*;
use nix_parser::*;
use std::fs::File;
use std::io::prelude::*;
use std::path::Path;
use itertools::Itertools;
use std::iter;

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
        .map(|nix_expr| {
            println!("{:?}", nix_expr);
            nix_expr.pretty_format(0)
        });

    println!("---------------------------------------------------- Pretty -------------------------------");
    println!("{:}", res.unwrap());
}

impl PrettyFormat for NixExpr {
    fn pretty_format(&self, indent_level:i32) -> String {
        match *self {
            NixExpr::Assert(_, _) => format!("assert"),
            NixExpr::NamedFunc(_, _) => format!("namedFunc"),
            NixExpr::AnonLambda(ref formals, ref body) => format!("{{ {:} }}:\n{:}", formals.pretty_format(indent_level), body.pretty_format(indent_level)),
            NixExpr::If(_, _, _) => format!("If"),
            NixExpr::LambdaNamedAfter(_, _, _) => format!("LambdaNamedAfter"),
            NixExpr::LambdaNamedBefore(_, _, _) => format!("LambdaNamedBefore"),
            NixExpr::With(_, _) => format!("With"),
            NixExpr::Let(_, _) => format!("Let"),
            NixExpr::Value(_) => format!("Value"),
            NixExpr::Application(ref expr_selects) => expr_selects.pretty_format(indent_level),
        }
    }
}

impl PrettyFormat for NixValue {
    fn pretty_format(&self, indent_level:i32) -> String {
        match *self {
            NixValue::String(ref str) => format!("\"{:}\"", str),
            NixValue::Null => "null".to_string(),
            NixValue::Integer(int) => int.to_string(),
            NixValue::Boolean(false) => "false".to_string(),
            NixValue::Boolean(true) => "true".to_string(),
            NixValue::Path(ref str) => str.to_string(),
            NixValue::Ident(ref id) => id.pretty_format(indent_level),
            NixValue::List(ref values) => values.pretty_format(indent_level),
            NixValue::RecBinding(ref bindings) => format!("{:}rec {{\n{:}\n}}", indent(indent_level), bindings.pretty_format(indent_level + 1)),
            NixValue::CurlyBinds(ref bindings) => format!("{{\n{:}\n{:}}}", bindings.pretty_format(indent_level + 1), indent(indent_level)),
        }
    }
}

impl PrettyFormat for NixStringAttr {
    fn pretty_format(&self, indent_level:i32) -> String {
        match *self {
            NixStringAttr::String(ref str) => str.to_string(),
            NixStringAttr::Expr(ref expr) => expr.pretty_format(indent_level)
        }
    }
}

impl PrettyFormat for Vec<NixAttrElem> {
    fn pretty_format(&self, indent_level:i32) -> String {
        (*self).iter()
            .map(|elem| elem.pretty_format(indent_level))
            .join("\n")
    }
}

impl PrettyFormat for NixAttrElem {
    fn pretty_format(&self, indent_level:i32) -> String {
        match *self {
            NixAttrElem::Attr(ref id) => id.pretty_format(indent_level),
            NixAttrElem::StringAttr(ref string_attr) => string_attr.pretty_format(indent_level)
        }
    }
}

impl PrettyFormat for NixAttrPath {
    fn pretty_format(&self, indent_level:i32) -> String {
        match *self {
            NixAttrPath::Simple(ref attr_elem) => attr_elem.pretty_format(indent_level),
            NixAttrPath::Path(ref attr_elems) => attr_elems.pretty_format(indent_level)
        }
    }
}

fn indent(indent_level:i32) -> String {
    let space_for_indent = 2;
    iter::repeat(' ')
        .take(indent_level as usize * space_for_indent)
        .collect()
}

impl PrettyFormat for NixBinding {
    fn pretty_format(&self, indent_level: i32) -> String {
        format!("{:}{:} = {:};", indent(indent_level), self.lhs.pretty_format(indent_level), self.rhs.pretty_format(indent_level))
    }
}

impl PrettyFormat for Vec<NixBinding> {
    fn pretty_format(&self, indent_level: i32) -> String {
        (*self).iter()
            .map(|elem| elem.pretty_format(indent_level))
            .join("\n")
    }
}

impl PrettyFormat for Vec<NixValue> {
    fn pretty_format(&self, indent_level: i32) -> String {
        (*self).iter()
            .map(|elem| elem.pretty_format(indent_level))
            .join(" ")
    }
}

impl PrettyFormat for NixExprSelect {
    fn pretty_format(&self, indent_level: i32) -> String {
        match *self {
            NixExprSelect::DotAccess(ref value, ref attr_path) => format!("{:}.{:}", value.pretty_format(indent_level), attr_path.pretty_format(indent_level)),
            NixExprSelect::Simple(ref value) => format!("{:}", value.pretty_format(indent_level))
        }
    }
}

impl PrettyFormat for Vec<NixExprSelect> {
    fn pretty_format(&self, indent_level: i32) -> String {
        (*self).iter()
            .map(|elem| elem.pretty_format(indent_level))
            .join(" ")
    }
}

impl PrettyFormat for Vec<NixFormal> {
    fn pretty_format(&self, indent_level: i32) -> String {
        (*self).iter()
            .map(|elem| elem.pretty_format(indent_level))
            .join(", ")
    }
}

impl PrettyFormat for NixFormal {
    fn pretty_format(&self, indent_level: i32) -> String {
        match *self {
            NixFormal::Ellipsis => "...".to_string(),
            NixFormal::Identifier(ref id) => id.pretty_format(indent_level),
            NixFormal::IdentifierWithDefault(ref id, ref expr) => format!("{:} ? {:}", id.pretty_format(indent_level), expr.pretty_format(indent_level))
        }
    }
}

impl PrettyFormat for NixIdentifier {
    fn pretty_format(&self, indent_level: i32) -> String {
        match *self {
            NixIdentifier::Ident(ref str) => str.to_string()
        }
    }
}


trait PrettyFormat {
    /// The first parameter is the indent level
    fn pretty_format(&self, i32) -> String;
}