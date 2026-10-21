//@ [lean] known-failure
//@ [!lean] skip
//@ charon-args=--precise-drops

// The byte-view builtin must not authorize the reverse conversion: arbitrary
// bytes need not be valid UTF-8. Transmutes still require a separate model.
pub unsafe fn reverse(bytes: &[u8]) -> &str {
    core::mem::transmute(bytes)
}
