//@ [!lean] skip
//@ charon-args=--include=core::str::traits::_::eq
#![feature(register_tool)]
#![register_tool(verify)]

// Extract the ordinary Rust implementation of PartialEq, whose two shared
// as_bytes calls must resolve to the executable byte-view builtin.
pub fn names_equal(left: &str, right: &str) -> bool {
    left == right
}

pub fn names_equal_method(left: &str, right: &str) -> bool {
    left.eq(right)
}

pub fn names_equal_trait(left: &str, right: &str) -> bool {
    <str as PartialEq<str>>::eq(left, right)
}

pub fn names_equal_ref_trait(left: &str, right: &str) -> bool {
    <&str as PartialEq<&str>>::eq(&left, &right)
}

#[verify::test]
pub fn literal_checks() {
    assert!(names_equal("name", "name"));
    assert!(!names_equal("name", "names"));
    assert!(names_equal_method("字段🦀é", "字段🦀é"));
    assert!(!names_equal_method("字段🦀é", "字段🦀è"));
    assert!(names_equal_trait("a\0b", "a\0b"));
    assert!(!names_equal_trait("a\0b", "a\0c"));
    assert!(names_equal_ref_trait("", ""));
    assert!(!names_equal_ref_trait("é", "e\u{301}"));
}

#[cfg(test)]
mod tests {
    #[test]
    fn exact_names() {
        super::literal_checks();
    }
}
