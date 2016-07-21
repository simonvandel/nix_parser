#[macro_use]
extern crate nom;

pub use nom::IResult;
use nom::{multispace, not_line_ending, line_ending, digit, is_alphanumeric, ErrorKind, is_alphabetic, InputLength, Err};
use std::str;
use std::fmt::*;


#[derive(PartialEq, Debug, Clone)]
pub enum NixExpr {
    If(Box<NixExpr>, Box<NixExpr>, Box<NixExpr>),
    // Matches: ID ':' expr_function
    NamedFunc(NixIdentifier, Box<NixExpr>),
    /// Anonymous lambda
    // Matches: '{' formals '}' ':' expr_function
    AnonLambda(Vec<NixFormal>, Box<NixExpr>),
    /// Named lambda with the pattern named after the formals
    /// Matches: '{' formals '}' '@' ID ':' expr_function
    LambdaNamedAfter(Vec<NixFormal>, NixIdentifier, Box<NixExpr>),
    /// Named lambda with the pattern named before the formals
    /// Matches: '{' formals '}' '@' ID ':' expr_function
    LambdaNamedBefore(Vec<NixFormal>, NixIdentifier, Box<NixExpr>),
    /// With
    /// Matches: WITH expr ';' expr_function
    With(Box<NixExpr>, Box<NixExpr>),
    /// Let
    /// Matches: LET binds IN expr_function
    Let(Vec<NixBinding>, Box<NixExpr>),
    Value(NixValue),
    /// Assert
    /// Matches: ASSERT expr ';' expr_function
    Assert(Box<NixExpr>, Box<NixExpr>),
    /// Some application of values
    /// For example in builtins.getEnv "CONFIG_FILE", the components are "builtins
    Application(Vec<NixExprSelect>)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixExprSelect {
    /// Represents "stdenv.mkDerivation"
    DotAccess(NixValue, Box<NixAttrPath>),
    /// Just a wrapper around a nix value
    Simple(NixValue)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixFormal {
    Ellipsis,
    Identifier(NixIdentifier),
    IdentifierWithDefault(NixIdentifier, NixExpr)
}

#[derive(PartialEq, Debug, Clone)]
pub struct NixBinding {
    lhs:NixAttrPath,
    rhs:NixExpr
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixAttrPath {
    /// Just an identifier
    Simple(NixAttrElem),
    /// Identifiers separated by dots
    Path(Vec<NixAttrElem>)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixAttrElem {
    /// Matches attr
    Attr(NixIdentifier),
    StringAttr(NixStringAttr)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixStringAttr {
    // attribute access wrapped in string
    // e.g. x."y z"
    String(String),
    // attribute that has an expression.
    // e.g. x.${2+2}
    Expr(NixExpr)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixIdentifier {
    Ident(String)
}

#[derive(PartialEq, Debug, Clone)]
pub enum NixValue {
    String(String),
    Null,
    Integer(i64),
    Boolean(bool),
    Path(String),
    Ident(NixIdentifier),
    List(Vec<NixValue>),
    RecBinding(Vec<NixBinding>),
    CurlyBinds(Vec<NixBinding>)
}

/*********************** Expressions *****************************/
// TODO: consider if it is a good idea to expect whitespace here instead of further down in the tree
named!(pub nix_expr<&[u8], NixExpr>,
    chain!(
        multispace? ~
        nix_comment? ~
        expr:
            // Note: the order is important. It should at best follow the reference grammar
            alt_complete!(
                nix_named_func
            |   nix_anon_lambda
            |   nix_lambda_named_pattern_after
            |   nix_lambda_named_pattern_before
            |   nix_assert
            |   nix_with
            |   nix_let
            |   nix_if
                // nix_expr_op needs to be right after nix_if, to have the same grammar semantics as the reference grammar
            |   nix_expr_op
            |   map!(nix_value, NixExpr::Value)
            ),

        || {println!("nix_func"); expr}
    )
);

fn trace<'a, O, F>(input: &'a[u8], msg:&str, parser: F) -> IResult<&'a[u8], O>
    where F: Fn(&'a[u8]) -> IResult<&[u8], O>,
          O: Debug{
    // try to run the parser on the input
    let res = parser(input);
    println!("----DEBUG----\n{:?}\ninput: {:?}\nparser result:{:?}\n-------------\n", msg, str::from_utf8(input), res);
    // just return the result of the parser
    res
}


// TODO: all operators
named!(pub nix_expr_op<&[u8], NixExpr>,
    map!(
        separated_nonempty_list!(
            multispace,
            call!(trace, "nix_expr_op: expr in chain", nix_expr_select)
        ),
        NixExpr::Application
    )
);

// TODO: missing case with or keyword
named!(pub nix_expr_select<&[u8], NixExprSelect>,
    alt_complete!(
        chain!(
            lhs:
                nix_value ~
            multispace? ~
            tag!(".") ~
            multispace? ~
            rhs:
                nix_attr_path,

            || NixExprSelect::DotAccess(lhs, Box::new(rhs))
        )
    |   map!(nix_value, NixExprSelect::Simple)
    )
);

// TODO: should this be expr_simple?
named!(pub nix_value<&[u8], NixValue>,
    map!(
        alt_complete!(
        // all parsers just matching on keywords are to be parsed first
            nix_null
        |   nix_boolean
        |   nix_integer
        |   nix_string
        |   nix_path
        |   nix_rec_binding
        |   nix_curly_binding
        |   nix_list
        // identifier is the last option so it does not interfere with keyword parsers like null and boolean
        |   map!(call!(trace, "nix_value: ident", nix_identifier), NixValue::Ident)
        ),
        |val| {
            //println!("nix_value");
            val
        }
    )
);
/*****************************************************************/

named!(pub nix_comment<&[u8], ()>,
    alt_complete!(
        nix_single_line_comment
    )
);

named!(pub nix_single_line_comment<&[u8], ()>,
    chain!(
        char!('#') ~
        // match until a line ending is met
        not_line_ending ~
        // then consume the line ending
        line_ending,

        || {}
    )
);

named!(pub nix_curly_binding<&[u8], NixValue>,
    chain!(
        tag!("{") ~
        bindings:
            nix_bindings ~
        tag!("}"),

        || NixValue::CurlyBinds(bindings)
    )
);

named!(pub nix_rec_binding<&[u8], NixValue>,
    chain!(
        tag!("rec") ~
        multispace? ~
        tag!("{") ~
        bindings:
            nix_bindings ~
        tag!("}"),

        || NixValue::RecBinding(bindings)
    )
);


/*********************** Strings *****************************/
/// There are two syntactic variants of strings:
///  - Single line - denoted with double quotation marks e.g "this is a string"
///  - Multi line - denoted with two single quotation marks e.g ''this is a string''
named!(pub nix_string<&[u8], NixValue>,
    alt_complete!(
        nix_single_line_string
    )
);

named!(nix_single_line_string<&[u8], NixValue>,
    alt_complete!(
        empty_single_line_string
    |   inhabited_single_line_string
    )
);

named!(empty_single_line_string<&[u8], NixValue>,
    chain!(
        char!('\"') ~
        char!('\"'),

        || {println!("empty_single_line_string");NixValue::String("".to_string())}
    )
);

fn inhabited_single_line_string(input: &[u8]) -> IResult<&[u8], NixValue> {
    let (i, str_content): (&[u8], String) = try_parse!(input,
        delimited!(
            char!('"'),
            inside_string,
            char!('"')
        )

    );
    let nix_string = NixValue::String(str_content);
    IResult::Done(i, nix_string)
}

fn inside_string(input: &[u8]) -> IResult<&[u8], String> {
    let (i, str_content): (&[u8], &str) = try_parse!(input,
        apply!(take_until_non_escaped_char,'\"')
    );
    let string = str_content.to_string();
    IResult::Done(i, string)
}

/// read input up to the first occurrence of the provided char that is not escaped
fn take_until_non_escaped_char(input: &[u8], stop_char: char) -> IResult<&[u8], &str> {
    // determines whether the next character is escaped
    let mut next_is_escaped = false;

    let mut helper = |c: u8| {
        match c as char {
            // an escape character is found, so remember this
            '\\' => {
                next_is_escaped = true;
                // continue to the next char
                true
            },

            // stop char that is escaped, read more
            x if x == stop_char && next_is_escaped => {
                next_is_escaped = false;
                true
            },
            // stop char that is not escaped, so stop reading
            x if x == stop_char => false,

            // any other char, keep reading
            // we know that it is not escaped, so reset the escaped bool
            _ => {
                next_is_escaped = false;
                true
            }
        }
    };

    let (i, str_content): (&[u8], &str) = try_parse!(input,
        map_res!(
            take_while!(
                helper
            ),
            str::from_utf8
        )
    );

    IResult::Done(i, str_content)
}

/*************************************************************/


/*********************** Null *******************************/
named!(pub nix_null<&[u8], NixValue>,
    map!(
        tag!("null"),
        |_| NixValue::Null
    )
);
/*************************************************************/

/*********************** Integers ****************************/
named!(pub nix_integer<&[u8], NixValue>,
    map_res!(
        digit,
        |digits:&[u8]| {
            // TODO real error messages instead of just zero
            str::from_utf8(digits)
                .map_err(|_| 0)
                .and_then(|digit_str:&str| digit_str.parse::<i64>()
                    .map_err(|_| 0)
                )
                .map(NixValue::Integer)
        }
    )
);
/*************************************************************/

/*********************** Booleans ****************************/
named!(pub nix_boolean<&[u8], NixValue>,
    alt_complete!(
        map!(tag!("false"), |_| NixValue::Boolean(false))
    |   map!(tag!("true"), |_| NixValue::Boolean(true))
    )
);
/*************************************************************/

/*********************** Paths *******************************/
/// Parses 1 byte if the predicate returns true
fn satisfy<F>(input: &[u8], predicate: F) -> IResult<&[u8], u8>
    where F: Fn(u8) -> bool {
    let input_length = input.input_len();
    if input_length == 0 {
        // TODO: use more sane error message instead of zero
        return IResult::Error(Err::Code(ErrorKind::Custom(0)));
    }

    if predicate(input[0]) {
        // consume the first byte
        IResult::Done(&input[1..], input[0])
    } else {
        // consume nothing
        // TODO: use more sane error message instead of zero
        return IResult::Error(Err::Code(ErrorKind::Custom(0)));
    }
}

named!(path_char<&[u8], char>,
    alt_complete!(
        map!(apply!(satisfy, is_alphanumeric), |x:u8| x as char)
    |   char!('.')
    |   char!('_')
    |   char!('-')
    |   char!('+')
    )
);

/// A nix path.
/// Encodes this regex taking from https://github.com/NixOS/nix/blob/master/doc/manual/nix-lang-ref.xml :
/// [a-zA-Z0-9\.\_\-\+]*(\/[a-zA-Z0-9\.\_\-\+]+)+
named!(pub nix_path<&[u8], NixValue>,
    chain!(
        part1:
            map!(
                many0!(path_char),
                |x:Vec<char>| x.into_iter().collect::<String>()
            ) ~
        part2:
            map!(
                many1!(
                    chain!(
                        label1:
                            map!(
                                char!('/'),
                                |c:char|  {
                                    let res:String = c.to_string();
                                    res
                                }
                            ) ~
                        label2:
                            map!(
                                many1!(
                                    path_char
                                ),
                                |x:Vec<char>| x.into_iter().collect::<String>()
                            ),

                        || {label1 + &label2}
                    )
                ),
                |x:Vec<String>| x.into_iter().collect::<String>()
            ),

        || {NixValue::Path(part1 + &part2)
        }
    )
);
/*************************************************************/

/*********************** Assert ****************************/
named!(pub nix_assert<&[u8], NixExpr>,
    chain!(
        tag!("assert") ~
        condition: nix_expr ~
        tag!(";") ~
        result: nix_expr,

        || {
            NixExpr::Assert(Box::new(condition), Box::new(result))
        }
    )
);
/*************************************************************/

/// Errors when a reserved word is encountered. Does not consume any input.
/// Useful for preventing a parser to consume too much.
fn not_reserved<'a>(input: &'a[u8]) -> IResult<&'a[u8], ()> {
    let reserved = [ "let", "in"
        , "if", "then", "else"
        , "assert"
        , "with"
        , "rec"
        , "inherit"
        , "or"
    ];
    let (_, next_word):(_, &[u8]) = try_parse!(input,
        peek!(is_not!(" \n\t\r"))
    );
    if reserved.contains(&str::from_utf8(next_word).unwrap()) {
        IResult::Error(Err::Code(ErrorKind::Custom(0)))
    } else {
        IResult::Done(input, ())
    }
}

/*********************** Identifier **************************/
/// A nix identifier
/// Regex from https://github.com/NixOS/nix/blob/06068b353d7867d0e0299d4285e9b1a46195144c/src/libexpr/lexer.l :
/// [a-zA-Z\_][a-zA-Z0-9\_\'\-]*
named!(pub nix_identifier<&[u8], NixIdentifier>,
    chain!(
        not_reserved ~
        res: chain!(
                part1:
                    map!(
                        apply!(satisfy, |c| is_alphabetic(c) || c == ('_' as u8) ),
                        |c:u8| (c as char).to_string()
                    ) ~
                part2:
                    map_res!(
                        many0!(
                            apply!(satisfy, |c|
                                is_alphanumeric(c)
                                || c == ('_' as u8)
                                || c == ('\'' as u8)
                                || c == ('-' as u8)
                            )
                        ),
                        String::from_utf8
                    ),

                || {
                    let res = NixIdentifier::Ident(part1 + &part2);
                    //println!("nix_identifier found: {:?}", res);
                    res

                }
        ),

        || res
    )

);
/*************************************************************/

/*********************** If **********************************/
/// An if expression
named!(pub nix_if<&[u8], NixExpr>,
    chain!(
        tag!("if") ~
        multispace ~
        condition:
            nix_expr ~
        multispace ~
        tag!("then") ~
        multispace ~
        true_case:
            nix_expr ~
        multispace ~
        tag!("else") ~
        multispace ~
        false_case:
            nix_expr,

        || {
            NixExpr::If(Box::new(condition), Box::new(true_case), Box::new(false_case))
        }
    )
);
/*************************************************************/

named!(nix_formals<&[u8], Vec<NixFormal> >,
    chain!(
        mut formals1:
            separated_nonempty_list!(
                chain!(
                    multispace? ~
                    tag!(",") ~
                    multispace?,
                    || {}
                ),
                nix_formal
            ) ~
        // match potential end comma and ellipsis
        multispace? ~
        tag!(",")? ~
        multispace? ~
        ellipsis:
            tag!("...")? ,

        || {
            if ellipsis.is_some() {
                formals1.push(NixFormal::Ellipsis)
            }
            formals1

        }
    )
);

named!(nix_formal<&[u8], NixFormal>,
    alt_complete!(
        map!(nix_identifier, NixFormal::Identifier)
    |   chain!(
            id:
                nix_identifier ~
            tag!("?") ~
            expr: nix_expr,

            || NixFormal::IdentifierWithDefault(id, expr)
        )
    )
);

named!(pub nix_lambda_named_pattern_after<&[u8], NixExpr>,
    chain!(
        tag!("{") ~
        multispace? ~
        formals:
            nix_formals ~
        multispace? ~
        tag!("}") ~
        multispace? ~
        tag!("@") ~
        multispace? ~
        id:
            nix_identifier ~
        // This space is mandatory to distinguish IDs from URIs
        multispace ~
        tag!(":") ~
        multispace? ~
        expr:
            nix_expr,

        || NixExpr::LambdaNamedAfter(formals, id, Box::new(expr))
    )
);

named!(pub nix_lambda_named_pattern_before<&[u8], NixExpr>,
    chain!(
        id:
            nix_identifier ~
        multispace? ~
        tag!("@") ~
        multispace? ~
        tag!("{") ~
        multispace? ~
        formals:
            nix_formals ~
        multispace? ~
        tag!("}") ~
        multispace? ~
        tag!(":") ~
        multispace? ~
        expr:
            nix_expr,

        || NixExpr::LambdaNamedBefore(formals, id, Box::new(expr))
    )
);

named!(pub nix_anon_lambda<&[u8], NixExpr>,
    chain!(
        tag!("{") ~
        multispace? ~
        formals:
            nix_formals ~
        multispace? ~
        tag!("}") ~
        multispace? ~
        tag!(":") ~
        multispace? ~
        expr:
            nix_expr,

        || NixExpr::AnonLambda(formals, Box::new(expr))
    )
);


// TODO:  we do not match OR_KW (yet) (see https://github.com/NixOS/nix/issues/975)
named!(nix_attr<&[u8], NixIdentifier>,
    alt_complete!(
        nix_identifier
    )
);

named!(nix_string_attr<&[u8], NixStringAttr>,
    alt_complete!(
        map_res!(nix_single_line_string, |val| {
            match val {
                NixValue::String(str) => Ok(NixStringAttr::String(str)),
                _ => Err("This should really not happen. Only a String should be possible")
            }
        })
    |   chain!(
            tag!("${") ~
            expr: nix_expr ~
            tag!("}"),

            || NixStringAttr::Expr(expr)
        )
    )
);

named!(nix_attr_path<&[u8], NixAttrPath>,
    map!(
        separated_nonempty_list!(
            chain!(
                multispace? ~
                tag!(".") ~
                multispace?,
                || {}
            ),
            alt_complete!(
                map!(nix_attr, NixAttrElem::Attr)
            |   map!(nix_string_attr, NixAttrElem::StringAttr)
            )
        ),
        |path:Vec<NixAttrElem>| {
            // If the path contains only 1 element, we can make it into a simple path
            if path.len() == 1 {
                NixAttrPath::Simple(path[0].clone())
            } else {
                NixAttrPath::Path(path)
            }
        }
    )
);

// TODO: binds with inherit
named!(nix_binding<&[u8], NixBinding>,
    chain!(
        lhs:
            nix_attr_path ~
        multispace? ~
        tag!("=") ~
        multispace? ~
        rhs: nix_expr ~
        multispace? ~
        tag!(";"),

        || {println!("nix_binding");NixBinding {lhs:lhs, rhs: rhs}}
    )
);

named!(nix_bindings<&[u8], Vec<NixBinding> >,
    many0!(
        chain!(
            multispace? ~
            binding: nix_binding ~
            multispace?,
            || binding
        )
    )
);

/*********************** Let **********************************/
/// A let expression
named!(pub nix_let<&[u8], NixExpr>,
    chain!(
        tag!("let") ~
        bindings:
            nix_bindings ~
        tag!("in") ~
        // There should always be space after 'in'
        multispace ~
        expr:
            nix_expr,

        || {
            println!("nix_let");
            NixExpr::Let(bindings, Box::new(expr))
        }
    )
);
/*************************************************************/

/*********************** With **********************************/
/// A with expression
named!(pub nix_with<&[u8], NixExpr>,
    chain!(
        tag!("with") ~
        lhs_expr:
            nix_expr ~
        tag!(";") ~
        rhs_expr:
            nix_expr,

        || {
            NixExpr::With(Box::new(lhs_expr), Box::new(rhs_expr))
        }
    )
);
/*************************************************************/

/*********************** NamedFunc **********************************/
/// A named function
named!(pub nix_named_func<&[u8], NixExpr>,
    chain!(
        name:
            nix_identifier ~
        multispace? ~
        tag!(":") ~
        expr:
            nix_expr,

        || {
            NixExpr::NamedFunc(name, Box::new(expr))
        }
    )
);
/*************************************************************/

/*********************** List **********************************/
/// A list
named!(pub nix_list<&[u8], NixValue>,
    chain!(
        tag!("[") ~
        content: many0!(
            chain!(
                // each element is separated by whitespace
                multispace? ~
                value: nix_value ~
                multispace?,

                || value
            )

        ) ~
        tag!("]"),

        || {
            NixValue::List(content)
        }
    )
);
/*************************************************************/
#[cfg(test)]
mod tests {
    use super::*;

    // Helper macro for defining parser tests
    macro_rules! mk_parse_test {
        ( name: $testName:ident, case: $test_case:expr, expected: $expected:expr, func: $test_fn:expr ) => {
            #[test]
            fn $testName () {
                let res = $test_fn(include_bytes!($test_case));
                match res {
                    IResult::Done(x, ref output) if x.is_empty() => assert_eq!($expected, *output),
                    IResult::Done(not_consumed, _) =>
                        panic!("Reached Done, but did not consume the whole input file. Not consumed: {:?}", not_consumed),
                    IResult::Incomplete(rest) => panic!("Incomplete with rest: {:?}", rest),
                    IResult::Error(err) => panic!("Incomplete with rest: {:?}", err)
                }
            }
        };
        ( name: $testName:ident, case: $test_case:expr, should_fail, func: $test_fn:expr ) => {
            #[test]
            #[should_panic]
            fn $testName () {
                let res = $test_fn(include_bytes!($test_case));
                match res {
                    // parsing was successful, which it should not be. Return without panicking
                    IResult::Done(_, _) => return,
                    IResult::Incomplete(rest) => panic!("Incomplete with rest: {:?}", rest),
                    IResult::Error(err) => panic!("Incomplete with rest: {:?}", err)
                }
            }
        }
    }

    mk_parse_test!(
        name: nix_empty_single_line_string,
        case: "../test_cases/strings/single_line_empty.nix",
        expected: NixValue::String("".to_string()),
        func: nix_string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string_no_whitespace,
        case: "../test_cases/strings/single_line_no_whitespace.nix",
        expected: NixValue::String("z".to_string()),
        func: nix_string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string,
        case: "../test_cases/strings/single_line1.nix",
        expected: NixValue::String("i am a string with whitespace".to_string()),
        func: nix_string
     );

    mk_parse_test!(
        name: nix_inhabited_escaped_quotation_single_line_string,
        case: "../test_cases/strings/single_line_escaped1.nix",
        expected: NixValue::String("x\\\"".to_string()),
        func: nix_string
     );

    mk_parse_test!(
        name: nix_inhabited_escaped_quotation2_single_line_string,
        case: "../test_cases/strings/single_line_escaped2.nix",
        expected: NixValue::String("x\\\"x".to_string()),
        func: nix_string
     );

    // TODO: multi-line strings

    mk_parse_test!(
        name: nix_null1,
        case: "../test_cases/null.nix",
        expected: NixValue::Null,
        func: nix_null
     );

    mk_parse_test!(
        name: nix_integer1,
        case: "../test_cases/integers/integer1.nix",
        expected: NixValue::Integer(123),
        func: nix_integer
     );

    mk_parse_test!(
        name: nix_boolean_true,
        case: "../test_cases/booleans/true.nix",
        expected: NixValue::Boolean(true),
        func: nix_boolean
     );

    mk_parse_test!(
        name: nix_boolean_false,
        case: "../test_cases/booleans/false.nix",
        expected: NixValue::Boolean(false),
        func: nix_boolean
     );

    mk_parse_test!(
        name: nix_path1,
        case: "../test_cases/paths/1.nix",
        expected: NixValue::Path("/bin".to_string()),
        func: nix_path
     );

    mk_parse_test!(
        name: nix_path2,
        case: "../test_cases/paths/2.nix",
        expected: NixValue::Path("/bin/sh".to_string()),
        func: nix_path
     );

    mk_parse_test!(
        name: nix_path3,
        case: "../test_cases/paths/3.nix",
        expected: NixValue::Path("./builder.sh".to_string()),
        func: nix_path
     );

    mk_parse_test!(
        name: nix_assert1,
        case: "../test_cases/asserts/1.nix",
        expected: {
            NixExpr::Assert(
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(false))))),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Null)))))
        },
        func: nix_assert
     );

    mk_parse_test!(
        name: nix_identifier1,
        case: "../test_cases/identifiers/1_ignore_validate.nix",
        expected: NixIdentifier::Ident("x".to_string()),
        func: nix_identifier
     );

    mk_parse_test!(
        name: nix_if1,
        case: "../test_cases/if/1.nix",
        expected:
            NixExpr::If(
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true))))),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(false))))),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(false))))),
        ),
        func: nix_if
     );

    mk_parse_test!(
        name: nix_with1,
        case: "../test_cases/with/1.nix",
        expected:
            NixExpr::With(
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(false))))),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true))))),
        ),
        func: nix_with
     );

    mk_parse_test!(
        name: nix_let1,
        case: "../test_cases/let/1.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Simple(NixAttrElem::Attr(NixIdentifier::Ident("x".to_string()))),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Ident(NixIdentifier::Ident("x".to_string())))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let2,
        case: "../test_cases/let/2.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Simple(NixAttrElem::Attr(NixIdentifier::Ident("x".to_string()))),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let3,
        case: "../test_cases/let/3.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Simple(NixAttrElem::Attr(NixIdentifier::Ident("x".to_string()))),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let4,
        case: "../test_cases/let/4.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Path(
                            vec!(
                                NixAttrElem::Attr(NixIdentifier::Ident("x".to_string())),
                                NixAttrElem::Attr(NixIdentifier::Ident("y".to_string()))
                            )
                        ),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let5,
        case: "../test_cases/let/5.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Path(
                            vec!(
                                NixAttrElem::Attr(NixIdentifier::Ident("x".to_string())),
                                NixAttrElem::Attr(NixIdentifier::Ident("y".to_string()))
                            )
                        ),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let6,
        case: "../test_cases/let/6.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Path(
                            vec!(
                                NixAttrElem::Attr(NixIdentifier::Ident("x".to_string())),
                                NixAttrElem::StringAttr(NixStringAttr::String("y z".to_string()))
                            )
                        ),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("".to_string())))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_let7,
        case: "../test_cases/let/7.nix",
        expected:
            NixExpr::Let(
                vec!(NixBinding{
                        lhs: NixAttrPath::Simple(NixAttrElem::Attr(NixIdentifier::Ident("x".to_string()))),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::List(vec!(NixValue::Integer(1))))))
                    }),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_let
     );

    mk_parse_test!(
        name: nix_rec_binding1,
        case: "../test_cases/rec_binding/1.nix",
        expected:
            NixValue::RecBinding(
                vec!(
                    NixBinding{
                        lhs: NixAttrPath::Simple(
                                NixAttrElem::Attr(NixIdentifier::Ident("name".to_string()))
                            ),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("hej".to_string())))))
                    }
                )
        ),
        func: nix_rec_binding
     );

    mk_parse_test!(
        name: nix_curly_binding1,
        case: "../test_cases/curly_binding/1.nix",
        expected:
            NixValue::CurlyBinds(
                vec!(
                    NixBinding{
                        lhs: NixAttrPath::Simple(
                                NixAttrElem::Attr(NixIdentifier::Ident("name".to_string()))
                            ),
                        rhs: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::String(("hej".to_string())))))
                    }
                )
        ),
        func: nix_curly_binding
     );

    mk_parse_test!(
        name: nix_func1,
        case: "../test_cases/func/1.nix",
        expected:
            NixExpr::NamedFunc(
                NixIdentifier::Ident("x".to_string())
                ,Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_named_func
     );

    mk_parse_test!(
        name: nix_func2,
        case: "../test_cases/func/2.nix",
        expected:
            NixExpr::NamedFunc(
                NixIdentifier::Ident("x".to_string())
                ,Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Integer(2))))),
        ),
        func: nix_named_func
     );

    mk_parse_test!(
        name: nix_list1,
        case: "../test_cases/list/1.nix",
        expected:
            NixValue::List(
                vec!(
                     NixValue::Integer(1)
                    ,NixValue::Integer(2)
                    ,NixValue::Integer(3)
                )
            ),
        func: nix_list
     );

    mk_parse_test!(
        name: nix_list2,
        case: "../test_cases/list/2.nix",
        expected:
            NixValue::List(
                vec!(
                     NixValue::Integer(1)
                )
            ),
        func: nix_list
     );

    mk_parse_test!(
        name: nix_list3,
        case: "../test_cases/list/3_ignore_validate.nix",
        expected:
            NixValue::List(
                vec!(
                     NixValue::Ident(NixIdentifier::Ident("stdenv".to_string()))
                )
            ),
        func: nix_list
     );

    mk_parse_test!(
        name: nix_anon_lambda1,
        case: "../test_cases/anon_lambda/1.nix",
        expected:
            NixExpr::AnonLambda(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string()))
                ),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_anon_lambda
     );

    mk_parse_test!(
        name: nix_anon_lambda2,
        case: "../test_cases/anon_lambda/2.nix",
        expected:
            NixExpr::AnonLambda(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_anon_lambda
     );

    mk_parse_test!(
        name: nix_anon_lambda3,
        case: "../test_cases/anon_lambda/3.nix",
        expected:
            NixExpr::AnonLambda(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_anon_lambda
     );

    mk_parse_test!(
        name: nix_anon_lambda4,
        case: "../test_cases/anon_lambda/4.nix",
        expected:
            NixExpr::AnonLambda(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string())),
                     NixFormal::Ellipsis
                ),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_anon_lambda
     );

    mk_parse_test!(
        name: nix_anon_lambda5,
        case: "../test_cases/anon_lambda/5.nix",
        expected:
            NixExpr::AnonLambda(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_anon_lambda
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after1,
        case: "../test_cases/lambda_named_pattern_after/1.nix",
        expected:
            NixExpr::LambdaNamedAfter(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after2,
        case: "../test_cases/lambda_named_pattern_after/2.nix",
        expected:
            NixExpr::LambdaNamedAfter(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after3,
        case: "../test_cases/lambda_named_pattern_after/3.nix",
        expected:
            NixExpr::LambdaNamedAfter(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after4,
        case: "../test_cases/lambda_named_pattern_after/4.nix",
        expected:
            NixExpr::LambdaNamedAfter(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string())),
                     NixFormal::Ellipsis
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after5,
        case: "../test_cases/lambda_named_pattern_after/5.nix",
        expected:
            NixExpr::LambdaNamedAfter(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_after6,
        case: "../test_cases/lambda_named_pattern_after/6_should_fail_ignore_validate.nix",
        should_fail,
        func: nix_lambda_named_pattern_after
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_before1,
        case: "../test_cases/lambda_named_pattern_before/1.nix",
        expected:
            NixExpr::LambdaNamedBefore(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_before
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_before2,
        case: "../test_cases/lambda_named_pattern_before/2.nix",
        expected:
            NixExpr::LambdaNamedBefore(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_before
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_before3,
        case: "../test_cases/lambda_named_pattern_before/3.nix",
        expected:
            NixExpr::LambdaNamedBefore(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_before
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_before4,
        case: "../test_cases/lambda_named_pattern_before/4.nix",
        expected:
            NixExpr::LambdaNamedBefore(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string())),
                     NixFormal::Ellipsis
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_before
     );

    mk_parse_test!(
        name: nix_lambda_named_pattern_before5,
        case: "../test_cases/lambda_named_pattern_before/5.nix",
        expected:
            NixExpr::LambdaNamedBefore(
                vec!(
                     NixFormal::Identifier(NixIdentifier::Ident("name1".to_string())),
                     NixFormal::Identifier(NixIdentifier::Ident("name2".to_string()))
                ),
                NixIdentifier::Ident("func1".to_string()),
                Box::new(NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))))
            ),
        func: nix_lambda_named_pattern_before
     );

    mk_parse_test!(
        name: nix_comment1,
        case: "../test_cases/comments/1.nix",
        expected: NixExpr::Application(vec!(NixExprSelect::Simple(NixValue::Boolean(true)))),
        func: nix_expr
     );

    mk_parse_test!(
        name: nix_expr_select1,
        case: "../test_cases/expr_select/1_ignore_validate.nix",
        expected: NixExprSelect::DotAccess(
            NixValue::Ident(NixIdentifier::Ident("stdenv".to_string())),
            Box::new(NixAttrPath::Simple(
                                NixAttrElem::Attr(NixIdentifier::Ident("mkDerivation".to_string()))
                            )
                        )
            ),
        func: nix_expr_select
     );
}