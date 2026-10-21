import Aeneas.Std.String
import Aeneas.Std.Core.Iter

namespace Aeneas.Std

/-- The remaining Unicode scalar values of Rust's shared character iterator. -/
@[rust_type "core::str::iter::Chars" (body := .opaque)]
structure core.str.iter.Chars where
  remaining : List Char

@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::next"]
def core.str.iter.IteratorChars.next (it : core.str.iter.Chars) : RustM ((Option Char) × core.str.iter.Chars) :=
  match it.remaining with
  | [] => .ok (none, it)
  | c :: cs => .ok (some c, ⟨cs⟩)

@[reducible, rust_trait_impl
  "core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>"]
def core.iter.traits.iterator.IteratorChars :
  core.iter.traits.iterator.Iterator core.str.iter.Chars Char := {
  next := core.str.iter.IteratorChars.next
}

@[rust_fun "core::str::iter::{core::iter::traits::iterator::Iterator<core::str::iter::Chars<'a>, char>}::collect"]
def core.str.iter.IteratorChars.collect
  {B : Type} (inst : core.iter.traits.collect.FromIterator B Char)
  (it : core.str.iter.Chars) : RustM B :=
  core.iter.traits.iterator.Iterator.collect.default
    core.iter.traits.iterator.IteratorChars inst it

@[rust_fun "core::str::{str}::chars"]
def core.str.Str.chars (s : Str) : RustM core.str.iter.Chars :=
  .ok ⟨s.toString.toList⟩

@[simp] theorem core.str.Str.chars_eq (s : Str) :
    chars s = .ok ⟨s.toString.toList⟩ := rfl

@[simp] theorem core.str.iter.IteratorChars.next_nil :
    next ⟨[]⟩ = .ok (none, ⟨[]⟩) := rfl

@[simp] theorem core.str.iter.IteratorChars.next_cons (c : Char) (cs : List Char) :
    next ⟨c :: cs⟩ = .ok (some c, ⟨cs⟩) := rfl

end Aeneas.Std
