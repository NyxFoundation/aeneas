//@ [!lean] skip

pub trait WithSlice {
    const SLICE: &'static [u16];
}

/*struct S;
impl WithSlice for S {
    const SLICE : &'static [u16] = &[0, 1];
}

impl S {
    fn read(i : usize) -> u16 {
        S::SLICE[i]
    }

    fn sum() -> u16 {
        let mut s = 0;
        for x in Self::SLICE {
            s += x;
        }
        s
    }
}
*/

fn read<S: WithSlice>(_: S, i: usize) -> u16 {
    S::SLICE[i]
}

/*fn sum<S : WithSlice>(_ : S, i : usize) -> u16 {
    let mut s = 0;
    for x in S::SLICE {
        s += x;
    }
    s
}*/

fn use_static() {
    const PREFIX: &[u8; 1] = &[0];
    let _ = PREFIX;
}

#[derive(Clone, Copy)]
pub enum Declaration {
    Boolean,
    Vector(&'static Declaration, usize),
}

pub fn declaration_width(declaration: &Declaration) -> Option<usize> {
    match *declaration {
        Declaration::Boolean => Some(1),
        Declaration::Vector(element, count) => match declaration_width(element) {
            Some(width) => width.checked_mul(count),
            None => None,
        },
    }
}

pub fn declaration_valid(declaration: &Declaration) -> Result<(), ()> {
    match *declaration {
        Declaration::Boolean => Ok(()),
        Declaration::Vector(element, count) => {
            if count == 0 {
                return Err(());
            }
            declaration_valid(element)
        }
    }
}

#[test]
fn should_follow_nested_static_references_without_losing_their_loan() {
    const BOOLEAN: Declaration = Declaration::Boolean;
    const PAIR: Declaration = Declaration::Vector(&BOOLEAN, 2);
    const NESTED: Declaration = Declaration::Vector(&PAIR, 4);
    const EMPTY: Declaration = Declaration::Vector(&PAIR, 0);
    assert_eq!(declaration_width(&NESTED), Some(8));
    assert_eq!(declaration_valid(&NESTED), Ok(()));
    assert_eq!(declaration_valid(&EMPTY), Err(()));
}
