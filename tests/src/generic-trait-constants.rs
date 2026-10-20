//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

pub trait HasWidth {
    const WIDTH: usize;
}

pub struct Byte;

impl HasWidth for Byte {
    const WIDTH: usize = 7;
}

pub fn aggregate<T: HasWidth>() -> (usize, usize) {
    (T::WIDTH, 9)
}

pub fn repeated<T: HasWidth>() -> [usize; 2] {
    [T::WIDTH; 2]
}

fn identity(value: usize) -> usize {
    value
}

pub fn argument<T: HasWidth>() -> usize {
    identity(T::WIDTH)
}

pub enum Descriptor {
    Byte,
    Vector(&'static Descriptor, usize),
}

pub trait Describe {
    const DESC: &'static Descriptor;
}

impl Describe for Byte {
    const DESC: &'static Descriptor = &Descriptor::Byte;
}

pub struct Vector<T, const N: usize>(T, [(); N]);

impl<T: Describe, const N: usize> Describe for Vector<T, N> {
    const DESC: &'static Descriptor = &Descriptor::Vector(T::DESC, N);
}

pub fn descriptor<T: Describe>() -> &'static Descriptor {
    T::DESC
}

#[verify::test]
pub fn check_widths() {
    let pair = aggregate::<Byte>();
    assert!(pair.0 == 7 && pair.1 == 9);
    let array = repeated::<Byte>();
    assert!(array[0] == 7 && array[1] == 7);
    assert!(argument::<Byte>() == 7);
}

#[verify::test]
pub fn check_nested_descriptor() {
    match descriptor::<Vector<Byte, 3>>() {
        Descriptor::Vector(Descriptor::Byte, count) => assert!(*count == 3),
        _ => panic!("unexpected declaration"),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn should_preserve_generic_constant_values_when_they_are_embedded_in_operands() {
        super::check_widths();
    }

    #[test]
    fn should_preserve_nested_generic_static_descriptors_when_a_type_wraps_another() {
        super::check_nested_descriptor();
    }
}
