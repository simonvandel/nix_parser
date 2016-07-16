#[macro_use]
extern crate nom;

use nom::*;
use std::str;


#[derive(Eq, PartialEq, Debug)]
pub enum NixExpr {
    Function,
    Value(NixValue),
}

#[derive(Eq, PartialEq, Debug)]
pub enum NixValue {
    String(String),
    Null,
    Integer(i64),
    Boolean(bool)
}

/*********************** Strings *****************************/
/// There are two syntactic variants of strings:
///  - Single line - denoted with double quotation marks e.g "this is a string"
///  - Multi line - denoted with two single quotation marks e.g ''this is a string''
named!(pub string<&[u8], NixValue>,
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
    let (i, str_content): (&[u8],String) = try_parse!(input,
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
    let (i, str_content): (&[u8],&str) = try_parse!(input,
        apply!(take_until_non_escaped_char,'\"')
    );
    let string = str_content.to_string();
    IResult::Done(i, string)
}

/// read input up to the first occurence of the provided char that is not escaped
fn take_until_non_escaped_char(input: &[u8], stop_char:char) -> IResult<&[u8], &str> {
    println!("test: {:?}", input);
    // determines whether the next character is escaped
    let mut next_is_escaped = false;

    let mut helper = |c:u8| {
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

    let (i, str_content): (&[u8],&str) =  try_parse!(input,
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
named!(pub null<&[u8], NixValue>,
    map!(
        tag!("null"),
        |_| NixValue::Null
    )
);
/*************************************************************/

/*********************** Integers ****************************/
named!(pub integer<&[u8], NixValue>,
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
named!(pub boolean<&[u8], NixValue>,
    alt!(
        map!(tag!("false"), |_| NixValue::Boolean(false))
    |   map!(tag!("true"), |_| NixValue::Boolean(true))
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
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string_no_whitespace,
        case: "../test_cases/strings/single_line_no_whitespace.nix",
        expected: NixValue::String("z".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string,
        case: "../test_cases/strings/single_line1.nix",
        expected: NixValue::String("i am a string with whitespace".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_escaped_quotation_single_line_string,
        case: "../test_cases/strings/single_line_escaped1.nix",
        expected: NixValue::String("x\\\"".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_escaped_quotation2_single_line_string,
        case: "../test_cases/strings/single_line_escaped2.nix",
        expected: NixValue::String("x\\\"x".to_string()),
        func: string
     );

    // TODO: multi-line strings

    mk_parse_test!(
        name: nix_null,
        case: "../test_cases/null.nix",
        expected: NixValue::Null,
        func: null
     );

    mk_parse_test!(
        name: nix_integer1,
        case: "../test_cases/integers/integer1.nix",
        expected: NixValue::Integer(123),
        func: integer
     );

    mk_parse_test!(
        name: nix_boolean_true,
        case: "../test_cases/booleans/true.nix",
        expected: NixValue::Boolean(true),
        func: boolean
     );

    mk_parse_test!(
        name: nix_boolean_false,
        case: "../test_cases/booleans/false.nix",
        expected: NixValue::Boolean(false),
        func: boolean
     );
}