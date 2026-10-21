# Lean shared string byte views

`Aeneas.Std.Str` is `Slice U8`: it stores bytes, not Unicode scalar values.
`core.str.Str.as_bytes` is an executable builtin returning `.ok s`. The
`rust_fun` annotation generates its entry in `ExtractBuiltinLean.ml` through
`lake exe extract`; generated Rust function bodies are not patched.

The interpreter uses the actual Rust function signature
`fn<'a>(&'a str) -> &'a [u8]` and its normal function-call abstractions. Input
and output types are still checked independently. The returned shared view
retains its lifetime dependency on the input loan. No borrow, loan, type-equality,
or transmute checks were changed. In particular, reverse and mutable transmutes
are not authorized by this builtin.

## Extraction

Use normal opaque external extraction for `str::as_bytes`. To extract ordinary
Rust string equality, include `core::str::traits::_::eq`, but do not include the
body of `core::str::_::as_bytes`. The equality body then calls the byte-view
builtin and the existing slice equality model. Explicitly including the
transmute-containing `as_bytes` body still fails closed. The builtin is the
supported bridge, not a general transmute lowering.

Lean string literals require Lean escaping, not OCaml `Char.escaped` output.
The extractor preserves UTF-8 source bytes verbatim, escapes quotes and
backslashes, and uses Lean escapes for ASCII control bytes (including zero).
OCaml decimal escapes such as `\195` and `\000` are invalid Lean syntax;
escaping UTF-8 bytes individually as Unicode code points would also be wrong.
Other backends' escaping is unchanged.

## Regressions and proofs

- `tests/src/str-bytes.rs`: native const/runtime byte checks, ASCII, multibyte
  UTF-8, embedded zero, escaping, shared aliases, shared reborrowing of mutable
  input, and reuse of the original shared input across returned views.
- `tests/src/str-equality.rs`: ordinary equality and all three `PartialEq` call
  forms, including distinct Unicode names, embedded zero, and composed versus
  decomposed spellings. It transparently extracts Rust's equality implementation.
- `tests/src/str-transmute-unsupported.rs`: the reverse transmute must still fail
  with the existing unsupported-unary-operation diagnostic.
- `tests/lean/StrBytesProofs.lean`: kernel-checked exact equations for arbitrary
  symbolic slices, alias outputs, the retained mutable input state, complete
  byte lists, lengths, and every byte position. There is no UTF-8-validity
  premise, literal-specific assumption, or native proof tactic.
- `Aeneas/Std/String.lean`: exact builtin preservation and general laws relating
  `toStr` to Lean's UTF-8 encoder, with an explicit size premise. The generated
  `#assert` commands are execution regressions, not substitutes for these laws.

Regenerate with the pinned Charon and source-built Aeneas through the normal
`make test-str-bytes.rs`, `make test-str-equality.rs`, and
`make test-str-transmute-unsupported.rs` targets. Verify with
`cd tests/lean && lake build StrBytesProofs StrEquality`. Do not change the
Charon pin or Lean toolchain to run these tests.

## Representation limits and separate interpreter issues

`Str = Slice U8` overapproximates UTF-8 validity. This byte-view model is valid
on that entire representation; it does not authorize constructing Rust strings
from arbitrary byte slices. The existing `chars()` model treating bytes as
characters is **not repaired** and must not be used to justify Unicode name
observations. Byte equality observes exact names without normalization.

Two independently reproducible interpreter limitations were found while
probing broader lifetime shapes. Neither is bypassed here:

```rust
pub fn escaped_literal() -> &'static [u8] {
    "name".as_bytes()
}
```

Returning this borrowed string literal currently fails with
`There should be no bottoms in the value` in `InterpExpressions.ml`. The string
literal decomposition introduces local storage which cannot escape this way.
Local literal byte observations and parameterized returned views are covered
by the passing regressions above.

```rust
pub fn nested_mut_owner(s: &mut &str) -> usize {
    let text = &**s;
    let first = text.as_bytes();
    let second = text.as_bytes();
    let length = first.len() + second.len();
    *s = "replaced";
    length
}
```

This nested mutable-owner shape currently fails with
`Can't end abstraction 1 as it is set as non-endable` in `InterpBorrows.ml`.
The direct `&mut str` shared reborrow regression does pass and retains its
input state. These limitations need separate lifetime-model work if a consumer
requires them; they are not reasons to weaken the loan checks or erase names.
