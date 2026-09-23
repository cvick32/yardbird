/// Convert typed SMT array operators into the e-graph parser's operator form.
pub(crate) fn preprocess_array_expr(input: &str) -> String {
    let mut result = String::with_capacity(input.len() + 10);
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch != '(' {
            result.push(ch);
            continue;
        }

        result.push(ch);
        let mut op_name = String::new();
        while let Some(&next_ch) = chars.peek() {
            if next_ch.is_whitespace() || next_ch == ')' {
                break;
            }
            op_name.push(chars.next().unwrap());
        }

        let replacement = op_name
            .strip_prefix("Read_")
            .map(|sorts| ("Read", sorts))
            .or_else(|| op_name.strip_prefix("Write_").map(|sorts| ("Write", sorts)))
            .or_else(|| {
                op_name
                    .strip_prefix("ConstArr_")
                    .map(|sorts| ("ConstArr", sorts))
            });
        let Some((operator, sorts)) = replacement else {
            result.push_str(&op_name);
            continue;
        };
        let Some((index_sort, value_sort)) = sorts.split_once('_') else {
            result.push_str(&op_name);
            continue;
        };

        result.push_str(operator);
        result.push(' ');
        result.push_str(index_sort);
        result.push(' ');
        result.push_str(value_sort);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::preprocess_array_expr;

    #[test]
    fn expands_typed_array_operators() {
        assert_eq!(
            preprocess_array_expr("(Read_Int_Int (Write_Int_Int a i v) i)"),
            "(Read Int Int (Write Int Int a i v) i)"
        );
        assert_eq!(
            preprocess_array_expr("(ConstArr_Int_Array_Int_Int v)"),
            "(ConstArr Int Array_Int_Int v)"
        );
    }
}
