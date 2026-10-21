import StrBytes

open Aeneas Aeneas.Std

namespace str_bytes

/-- The extracted wrapper preserves arbitrary symbolic bytes, including inputs
    outside the UTF-8 subset overapproximated by the `Str` representation. -/
theorem bytes_exact (s : Str) : bytes s = RustM.ok s := rfl

theorem aliases_exact (s : Str) : aliases s = RustM.ok (s, s, s) := rfl

/-- The mutable input's returned state is retained unchanged by a shared view. -/
theorem shared_from_mut_exact (s : Str) :
    shared_from_mut s = RustM.ok (s, s) := rfl

/-- No byte, position, or length changes at the extracted call boundary. -/
theorem bytes_observation (s : Str) (bs : Slice U8)
    (h : bytes s = RustM.ok bs) :
    bs.val = s.val ∧ bs.val.length = s.val.length ∧
      ∀ i : Nat, bs.val[i]? = s.val[i]? := by
  simp only [bytes, core.str.Str.as_bytes, RustM.ok.injEq] at h
  rw [← h]
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- No UTF-8-validity premise or literal-specific assumption is needed. -/
theorem bytes_of_list (xs : List U8) (h : xs.length ≤ Usize.max) :
    bytes ⟨xs, h⟩ = RustM.ok ⟨xs, h⟩ := rfl

end str_bytes
