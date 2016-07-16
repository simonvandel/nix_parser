#[macro_use]
extern crate nom;

use nom::*;
use std::str;


#[derive(PartialEq, Debug)]
pub enum NixExpr {
    Func(NixFunc),
}

/// Structure inspired from https://github.com/NixOS/nix/blob/master/src/libexpr/parser.y
#[derive(PartialEq, Debug)]
pub enum NixFunc {
    // Matches: ID ':' expr_function
    Func(NixIdentifier, Box<NixFunc>),
    /// Anonymous lambda
    // Matches: '{' formals '}' ':' expr_function
    // TODO: LambdaAnon()
    /// Named lambda
    /// Matches: '{' formals '}' '@' ID ':' expr_function
    // TODO: Lambda()
    /// With
    /// Matches: WITH expr ';' expr_function
    With(Box<NixExpr>, Box<NixFunc>),
    // TODO: Let()
    Value(NixValue),
    /// Assert
    /// Matches: ASSERT expr ';' expr_function
    Assert(Box<NixExpr>, Box<NixExpr>),
    If(Box<NixExpr>, Box<NixExpr>, Box<NixExpr>)
}


#[derive(PartialEq, Debug)]
pub enum NixIdentifier {
    Ident(String)
}

#[derive(PartialEq, Debug)]
pub enum NixValue {
    String(String),
    Null,
    Integer(i64),
    Boolean(bool),
    Path(String)
}

/*********************** Expressions *****************************/
named!(pub nix_expr<&[u8], NixExpr>,
    map!(call!(nix_func), NixExpr::Func)
);


named!(pub nix_func<&[u8], NixFunc>,
    chain!(
        multispace? ~
        expr:
            alt!(
                nix_value
            |   nix_assert
            |   nix_if
            |   nix_with
            ) ~
        multispace?,

        || expr
    )
);

named!(pub nix_value<&[u8], NixFunc>,
    map!(
        alt!(
            nix_string
        |   nix_null
        |   nix_integer
        |   nix_boolean
        |   nix_path
        ),
        NixFunc::Value
    )
);
/*****************************************************************/

/*********************** Strings *****************************/
/// There are two syntactic variants of strings:
///  - Single line - denoted with double quotation marks e.g "this is a string"
///  - Multi line - denoted with two single quotation marks e.g ''this is a string''
named!(pub nix_string<&[u8], NixValue>,
    alt!(
        empty_single_line_string
    |   inhabited_single_line_string
    )
);

named!(empty_single_line_string<&[u8], NixValue>,
    chain!(
        char!('\"') ~
        char!('\"'),

        || {NixValue::String("".to_string())}
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
    println!("test: {:?}", input);
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
    alt!(
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
    alt!(
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
named!(pub nix_assert<&[u8], NixFunc>,
    chain!(
        tag!("assert") ~
        condition: nix_expr ~
        tag!(";") ~
        result: nix_expr,

        || {
            NixFunc::Assert(Box::new(condition), Box::new(result))
        }
    )
);
/*************************************************************/

/*********************** Identifier **************************/
/// A nix identifier
/// Regex from https://github.com/NixOS/nix/blob/master/doc/manual/nix-lang-ref.xml :
/// [a-zA-Z\_][a-zA-Z0-9\_\']*
named!(pub nix_identifier<&[u8], NixIdentifier>,
    chain!(
        part1:
            map!(
                apply!(satisfy, |c| is_alphabetic(c) || c == ('_' as u8) ),
                |c:u8| (c as char).to_string()
            )~
        part2:
            map_res!(
                many0!(
                    apply!(satisfy, |c| is_alphanumeric(c) || c == ('_' as u8) || c == ('\'' as u8))
                ),
                String::from_utf8
            ),

        || {
            NixIdentifier::Ident(part1 + &part2)
        }
    )
);
/*************************************************************/

/*********************** If **********************************/
/// An if expression
named!(pub nix_if<&[u8], NixFunc>,
    chain!(
        tag!("if") ~
        condition:
            nix_expr ~
        tag!("then") ~
        true_case:
            nix_expr ~
        tag!("else") ~
        false_case:
            nix_expr,

        || {
            NixFunc::If(Box::new(condition), Box::new(true_case), Box::new(false_case))
        }
    )
);
/*************************************************************/

/*********************** With **********************************/
/// An if expression
named!(pub nix_with<&[u8], NixFunc>,
    chain!(
        tag!("with") ~
        expr:
            nix_expr ~
        tag!(";") ~
        expr_func:
            nix_func,

        || {
            NixFunc::With(Box::new(expr), Box::new(expr_func))
        }
    )
);
/*************************************************************/
#[cfg(test)]
mod tests {
    use super::*;
    use nom::{IResult};

    // Helper macro for defining parser tests
    macro_rules! mk_parse_test {
        ( name: $testName:ident, case: $test_case:expr, expected: $expected:expr, func: $test_fn:expr ) => {
            #[test]
            fn $testName () {
                let res = $test_fn(include_bytes!($test_case));
                match res {
                    IResult::Done(_, output) => assert_eq!($expected, output),
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
            NixFunc::Assert(
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Boolean(false)))),
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Null))))
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
            NixFunc::If(
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Boolean(true)))),
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Boolean(false)))),
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Boolean(false)))),
        ),
        func: nix_if
     );

    mk_parse_test!(
        name: nix_with1,
        case: "../test_cases/with/1.nix",
        expected:
            NixFunc::With(
                Box::new(NixExpr::Func(NixFunc::Value(NixValue::Boolean(false)))),
                Box::new(NixFunc::Value(NixValue::Boolean(true))),
        ),
        func: nix_with
     );
}