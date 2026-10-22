# Lean strings: UTF-8 invariant, byte views and kernel-clean literals

## Representation and observation

`Aeneas.Std.Str` stores a `Slice U8` together with
`ByteArray.IsValidUTF8` for precisely those bytes. The predicate and Unicode
encoder/decoder are Lean 4.31's standard library definitions. This encodes Rust
`str`'s existing type invariant, not an additional metadata/CodecLaw domain
premise. Invalid UTF-8 cannot inhabit `Str` without proving a false proposition.
There is no ASCII, Latin-1, U32, source-literal-length or allocation-test-case cap:
the byte bound is the existing native `Usize.max` bound on slices.

`Str.toString` is a total observation into Lean `String`, using the stored
validity proof and `String.fromUTF8`. It does not replace malformed sequences,
normalize names, project to characters-as-bytes, hash, or erase names. The
`toString_bytes`, `toString_byte_list`, `toString_length` and
`toString_injective` laws establish exact byte/order/length preservation and
injectivity. `toStr s h` admits every Lean string whose byte size is at most
`Usize.max`; it has an explicit size argument and no native-proof default.
Both conversion round trips are proved. No caller-side UTF-8 premise is needed.

## Shared byte view and borrowing

`core.str.Str.as_bytes` is an executable builtin returning `.ok s.bytes`.
Its `rust_fun` annotation generates the entry in `ExtractBuiltinLean.ml` via
`lake exe extract`; generated Rust function bodies are not patched.

The interpreter uses the actual Rust signature
`fn<'a>(&'a str) -> &'a [u8]` and ordinary function-call abstractions. The output
retains its lifetime dependency on the input loan. No borrow, loan, type-equality
or transmute checks have been changed. Reverse and mutable transmutes are not
authorized by this builtin.

Use normal opaque external extraction for `str::as_bytes`. To extract ordinary
Rust string equality, include `core::str::traits::_::eq`, but do not include the
transmute-containing `core::str::_::as_bytes` body. Equality then calls the byte
view and the existing slice equality model. Explicit transmute bodies remain
unsupported, not accepted through a general cast lowering.

## Literal construction and trust

The Lean backend emits `Str.ofBytes` applied to exact explicit `#u8` bytes,
a kernel-checked native-size proof, and a standard UTF-8 validity proof. For
example, the UTF-8 literal `é` is represented by bytes `[195#u8, 169#u8]`; its
validity witness is `[Char.ofNat 233]`. Lean's kernel checks that the standard
UTF-8 encoder of this witness equals those bytes. The OCaml UTF-8 decoder only
supplies a witness: it is not a trusted validity or runtime-equality certificate.
Invalid frontend UTF-8 is rejected rather than silently replaced.

The old `toStr` default `by decide +native` is removed. Literal-containing
programs do not use a proof about opaque `String.toByteArray` reduction, nor a
native axiom, opaque proof or generated-body substitution. Quotes, backslashes,
control escapes and embedded zero become ordinary explicit bytes. Other
backends' literal emission is unchanged.

## Character iterator plumbing

The old byte-as-character `chars()` implementation is replaced. `Chars` stores
the remaining Unicode scalar values of `Str.toString.toList`, using Lean's
validated UTF-8 decoding. `next` consumes one scalar, not one byte. Specialized
`collect` is executable and delegates to the ordinary iterator/`FromIterator`
model instead of an opaque declaration. This repairs these modeled iterator
operations, not every unmodeled Rust character/string API.

## Regression and kernel audit

- `tests/src/str-bytes.rs`: native const/runtime checks, exact byte order,
  ASCII, multibyte UTF-8, empty strings, embedded zero, escapes, Unicode boundary
  scalars, shared aliases, shared reborrowing of mutable input and retained state.
- `tests/src/str-equality.rs`: ordinary equality and three `PartialEq` call forms;
  distinct Unicode names, embedded zero and composed/decomposed spellings.
- `tests/src/string-chars.rs`: Unicode scalar iteration and collection plumbing.
- `tests/src/str-transmute-unsupported.rs`: actual unsupported LLBC transmute
  rejection, using precise drops/elaborated MIR rather than an opaque intrinsic.
- `tests/lean/StrBytesProofs.lean`: symbolic laws and kernel proofs of the actual
  extracted `str_bytes.literal_checks` and equality-fixture program results;
  source-level original-string observation, Unicode iteration, and invalid UTF-8
  exclusion. The source-level observation covers all native-sized strings.
- `tests/lean/StrBytesAudit.lean`: audits all byte/equality fixture programs and
  proofs, the Unicode iterator/collection programs, the string model, and their
  generated auxiliaries. Compilation fails if any axiom other than
  `propext`, `Classical.choice`, or `Quot.sound` is reachable. In particular,
  `_native.decide.ax`, `ofReduceBool`, `sorryAx` and custom axioms are forbidden.

Regenerate through the normal pinned Charon/source-built Aeneas test targets.
Verify with `cd tests/lean && lake build StrBytesAudit` (also included in the
full default build). Generated `#assert` execution tests supplement, not replace,
the kernel proofs and program-definition axiom audit. Pins remain unchanged.
The unrelated legacy `string_chars.print_vec` printing fixture still depends on
its pre-existing opaque formatter type; it is not part of the UTF-8 program
axiom gate. No formatter/IO trust contract is changed by this repair.

## Remaining independent interpreter limitations

Two broader lifetime shapes remain unsupported, without weakening any checks:

```rust
pub fn escaped_literal() -> &'static [u8] {
    "name".as_bytes()
}
```

This fails with `There should be no bottoms in the value` in
`InterpExpressions.ml`. The interpreter's string-literal decomposition creates
local storage which cannot escape this way. Local literal observations and
parameterized returned strings/views are covered by the passing regressions.

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

This fails with `Can't end abstraction 1 as it is set as non-endable` in
`InterpBorrows.ml`. The direct `&mut str` shared reborrow is supported and its
retained input state is proved. These are separate lifetime-model limitations,
not reasons to restrict Unicode, erase names or weaken a correctness law.
