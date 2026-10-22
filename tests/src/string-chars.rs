//@ [!lean] skip

pub fn first_two(s: &str) -> (Option<char>, Option<char>) {
    let mut chars = s.chars();
    (chars.next(), chars.next())
}

fn collect() {
    let s = "é字段🦀";
    let _chs: Vec<char> = s.chars().collect();
}

fn print_vec() {
    let v = [1, 3, 2].to_vec();
    println!("{:?}", v);
}

#[cfg(test)]
mod tests {
    #[test]
    fn unicode_scalars_not_bytes() {
        assert_eq!(super::first_two("é🦀"), (Some('é'), Some('🦀')));
        assert_eq!(super::first_two("a\0é"), (Some('a'), Some('\0')));
        assert_eq!(super::first_two(""), (None, None));
        assert_eq!(super::first_two("e\u{301}"), (Some('e'), Some('\u{301}')));
        super::collect();
    }
}
