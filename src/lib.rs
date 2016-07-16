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
}


/*pub fn string(input: &[u8]) -> IResult<&[u8], NixValue> {
    let converter = |x: &[u8]| match x {
        _ if x.len() == 0 => {
            Result::Ok("".to_string())
        },
        // the utf8 validation is O(n). We can avoid that if we know it is valid utf8
        _ => {
            String::from_utf8(x.to_vec())
        }
    };
    let (i, string_content) = try_parse!(input,
        alt!(
            delimited!(
                char!('\"'),
                map_res!(
                    is_not!("\""),
                    converter
                ),
                char!('\"')
            ) |
            chain!(
                char!('\"') ~
                char!('\"'),

                || {"".to_string()}
            )
        )

    );
    let nix_string = NixValue::String(string_content);
    IResult::Done(i, nix_string)
}*/


/*********************** Strings *****************************/
// There are two syntactic variants of strings:
//  - Single line - denoted with double quotation marks e.g "this is a string"
//  - Multi line - denoted with two single quotation marks e.g ''this is a string''
named!(pub string<&[u8], NixValue>,
    alt!(
        empty_single_line_string
    |   dbg!(inhabited_single_line_string)
    )
);

/*named!(take_until_not_escaped_quotation_mark,
    many1!(
        switch!(peek!(take!(2)),
            x@b"\\\"" => value!(x)
        )
    )
)*/

// parses the inside of a string, taking escaped characters into consideration
/*
fn single_line_string_content(input: &[u8]) -> IResult<&[u8], String> {
    let (i, str_content) = try_parse!(input,
        map_res!(
            many1!(
                alt!(
                    space |
                    alphanumeric
                )
            ),
            |res:Vec<&[u8]>| {String::from_utf8(res.concat())}
        )
    );
    IResult::Done(i, str_content)
}*/

fn inhabited_single_line_string(input: &[u8]) -> IResult<&[u8], NixValue> {
    println!("inhabited_single_line_string: {:?}", input);
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

fn allowed_char_in_string(input: &[u8]) -> IResult<&[u8], char> {
    println!("allowed_char_in_string: {:?}", input);
    let (i, str_content): (&[u8],char) = try_parse!(input,
        map!(take!(1), |c:&[u8]| c[0] as char)
    );
    IResult::Done(i, str_content)
}

/*fn until_non_escaped_quotation(input:&[u8]) -> IResult<&[u8], String> {
    let mut next_is_escaped = false;
    let input_length = input.input_len();
    // index in input where the result should stop
    let mut res_stop_idx = 0;
    let mut done = false;

    for (idx, char) in input.iter_indices() {
        if done {
            break;
        }
        match char {
            // if we see a backslash, the next character is going to be escaped
            &b'\\' => next_is_escaped = true,
            // a double quote and we know it is escaped
            &b'\"' if next_is_escaped => next_is_escaped = false,
            // a non-escaped quote means we are at the end of the string
            &b'\"' => {
                res_stop_idx = idx-1;
                done = true;
            },
        }
    }
    let res_string = &input[0..res_stop_idx]
    IResult::Done(&input[res_stop_idx+1..input_length], )
}*/

fn test(input: &[u8]) -> IResult<&[u8], &str> {
    println!("test: {:?}", input);
    let mut next_is_escaped = false;

    let mut hej = |c:u8| {
        let ch = c as char;
        println!("inde i hej (c) {:?}", c);
        println!("inde i hej (ch) {:?}", ch);
        match ch {
            '\\' => {
                println!("setting escaped to true");
                next_is_escaped = true;
                // continue
                true
            },
            // quote that is escaped, so we can go on
            '\"' if next_is_escaped => {
                println!("saw escaped quotation, allowing");
                println!("reseting escaped to false");
                next_is_escaped = false;
                true
            },
            // quote that is not escaped, so do not move on
            '\"' => false,
            x => {
                println!("allowing {:?}", x);
                println!("reseting escaped to false");
                next_is_escaped = false;
                true
            }
        }
    };

    let (i, str_content): (&[u8],&str) =  try_parse!(input,
        map_res!(
            take_while!(
                hej
            ),
            str::from_utf8
        )
    );

    IResult::Done(i, str_content)
}

fn many_chars(input: &[u8]) -> IResult<&[u8], String> {
    println!("many_chars: {:?}", input);
    /*let (i, str_content): (&[u8],String) = try_parse!(input,
        dbg!(map!(
            many1!(
                dbg!(allowed_char_in_string)
            ),
            |x:Vec<char>| x.into_iter().collect()
        ))
    );*/
    let (i, str_content): (&[u8],&str) = try_parse!(input,
        test
    );
    let string = str_content.to_string();
    IResult::Done(i, string)
}

fn inside_string(input: &[u8]) -> IResult<&[u8], String> {
    println!("inside_string: {:?}", input);
    let (i, str_content): (&[u8],String) = try_parse!(input,
        many_chars
        /*map_res!(
            escaped!(
                many_chars,
                '\\',
                is_a_bytes!(b"\"n\\")
            ),
            |x:&[u8]| String::from_utf8(x.to_vec())
        )*/

    );
    IResult::Done(i, str_content)
}


/*fn string_content(input: &[u8]) -> IResult<&[u8], &str>{
    let mut next_is_escaped = false;
    let input_length = input.input_len();

    for (idx, char) in input.iter_indices() {
        match char {
            // if we see a backslash, the next character is going to be escaped
            &b'\\' => next_is_escaped = true,
            // a double quote and we know it is escaped
            &b'\"' if next_is_escaped => next_is_escaped = false,
            // a non-escaped quote means we are at the end of the string
            &b'\"' => IResult::Done(&input[idx-1..], ),


        }
    }
    IResult::Done(&input[input_length..], input)
}*/

named!(empty_single_line_string<&[u8], NixValue>,
    chain!(
        char!('\"') ~
        char!('\"'),

        || {NixValue::String("".to_string())}
    )
);
/*************************************************************/

fn space_or_alphanumeric(input:u8) -> bool {
    true//is_space(input) || is_alphanumeric(input)
}


named!(pub esc<&[u8], &[u8]>,
    escaped!(
        take_while!(space_or_alphanumeric),
        '\\',
        is_a_bytes!(b"\"n\\")
    )
);

#[cfg(test)]
mod tests {
    use super::*;
    use nom::{IResult};

    // Helper macro for defining parser tests
    macro_rules! mk_parse_test {
        ( name: $testName:ident, input: $input:expr, expected: $expected:expr, func: $test_fn:expr ) => {
            #[test]
            fn $testName () {
                let res = $test_fn($input);
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
        input: b"\"\"",
        expected: NixValue::String("".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string_no_whitespace,
        input: b"\"z\"",
        expected: NixValue::String("z".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_single_line_string,
        input: b"\"i am a string with whitespace\"",
        expected: NixValue::String("i am a string with whitespace".to_string()),
        func: string
     );

    mk_parse_test!(
        name: nix_inhabited_escaped_quotation_single_line_string,
        input: b"\"x\\\"\"",
        expected: NixValue::String("x\\\"".to_string()),
        func: string
     );

/*    mk_parse_test!(
        name: escaped_test,
        input: b"abc d\"",
        expected: b"abc d\"",
        func: esc
     );*/
}