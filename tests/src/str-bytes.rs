//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub const fn bytes(s: &str) -> &[u8] {
    s.as_bytes()
}

// Returning the original string must retain every Unicode name byte.
pub fn original(s: &str) -> &str {
    s
}

pub fn shared_from_mut(s: &mut str) -> &[u8] {
    s.as_bytes()
}

pub fn aliases(s: &str) -> (&str, &[u8], &[u8]) {
    let alias = s;
    let first = s.as_bytes();
    let second = alias.as_bytes();
    (alias, first, second)
}

// Keep the original shared borrow live across two returned byte views,
// then use it again after consuming those aliases.
pub fn loan_retention(s: &str) -> usize {
    let (original, first, second) = aliases(s);
    let length = first.len() + second.len();
    length + original.as_bytes().len()
}

#[verify::test]
pub fn literal_checks() {
    let a = "name".as_bytes();
    assert!(a.len() == 4);
    assert!(a[0] == 110);
    assert!(a[3] == 101);
    let u = original("é字段🦀").as_bytes();
    assert!(u.len() == 12);
    assert!(u[0] == 195);
    assert!(u[1] == 169);
    assert!(u[2] == 229);
    assert!(u[3] == 173);
    assert!(u[4] == 151);
    assert!(u[5] == 230);
    assert!(u[6] == 174);
    assert!(u[7] == 181);
    assert!(u[8] == 240);
    assert!(u[9] == 159);
    assert!(u[10] == 166);
    assert!(u[11] == 128);
    let z = "a\0é".as_bytes();
    assert!(z.len() == 4);
    assert!(z[0] == 97);
    assert!(z[1] == 0);
    assert!(z[2] == 195);
    assert!(z[3] == 169);
    assert!(bytes("").len() == 0);
    let escaped = "\"\\\n\r\t\u{7}\u{7f}".as_bytes();
    assert!(escaped.len() == 7);
    assert!(escaped[0] == 34);
    assert!(escaped[1] == 92);
    assert!(escaped[2] == 10);
    assert!(escaped[3] == 13);
    assert!(escaped[4] == 9);
    assert!(escaped[5] == 7);
    assert!(escaped[6] == 127);
    let limits = "\u{7ff}\u{800}\u{d7ff}\u{e000}\u{10ffff}".as_bytes();
    assert!(limits.len() == 15);
    assert!(limits[0] == 223);
    assert!(limits[1] == 191);
    assert!(limits[11] == 244);
    assert!(limits[14] == 191);
}

#[cfg(test)]
mod tests {
    use super::*;

    const UTF8: &[u8] = bytes("é字段🦀");

    #[test]
    fn exact_bytes() {
        literal_checks();
        assert_eq!(bytes("name"), b"name");
        assert_eq!(UTF8, b"\xc3\xa9\xe5\xad\x97\xe6\xae\xb5\xf0\x9f\xa6\x80");
        assert_eq!(bytes("a\0é"), b"a\0\xc3\xa9");
        for s in ["", "name", "é字段🦀", "a\0é", "e\u{301}"] {
            assert_eq!(original(s), s);
            let (original, first, second) = aliases(s);
            assert_eq!(original, s);
            assert_eq!(first, s.as_bytes());
            assert_eq!(second, first);
            assert_eq!(loan_retention(s), 3 * s.len());
            let mut owned = s.to_owned();
            assert_eq!(shared_from_mut(owned.as_mut_str()), s.as_bytes());
        }
    }
}
