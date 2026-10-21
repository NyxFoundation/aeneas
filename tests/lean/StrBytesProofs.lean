import StrBytes
import StrEquality
import StringChars

open Aeneas Aeneas.Std

namespace str_bytes

/-- Exact preservation for arbitrary strings; UTF-8 validity is inside `Str`. -/
theorem bytes_exact (s : Str) : bytes s = RustM.ok s.bytes := rfl

theorem aliases_exact (s : Str) : aliases s = RustM.ok (s, s.bytes, s.bytes) := rfl

theorem shared_from_mut_exact (s : Str) :
    shared_from_mut s = RustM.ok (s.bytes, s) := rfl

theorem bytes_observation (s : Str) (bs : Slice U8)
    (h : bytes s = RustM.ok bs) :
    bs.val = s.bytes.val ∧ bs.val.length = s.bytes.val.length ∧
      ∀ i : Nat, bs.val[i]? = s.bytes.val[i]? := by
  simp only [bytes, core.str.Str.as_bytes, RustM.ok.injEq] at h
  rw [← h]
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- The source-level original string remains observable, not a projection/hash.
    All native-sized Lean strings are included, with no UTF-8 domain premise. -/
theorem original_string (s : String) (h : s.toByteArray.size ≤ Usize.max) :
    ∃ r, original (toStr s h) = RustM.ok r ∧ r.toString = s :=
  ⟨toStr s h, rfl, Str.toString_toStr s h⟩

/-- These are actual extracted literal-containing program definitions. -/
theorem literal_checks_eq : literal_checks = RustM.ok () := by rfl

theorem equality_literal_checks_eq : str_equality.literal_checks = RustM.ok () := by rfl

/-- Source-level string observation of a complete Unicode name and embedded NUL. -/
def unicodeName : Str :=
  Str.ofBytes [195#u8, 169#u8, 229#u8, 173#u8, 151#u8, 230#u8, 174#u8, 181#u8,
    240#u8, 159#u8, 166#u8, 128#u8, 0#u8] (by scalar_tac)
    (.intro [Char.ofNat 233, Char.ofNat 23383, Char.ofNat 27573, Char.ofNat 129408,
      Char.ofNat 0] (by decide))

theorem unicode_original : original unicodeName = RustM.ok unicodeName := rfl

theorem unicode_original_observation : unicodeName.toString = "é字段🦀\x00" := rfl

theorem unicode_bytes : (unicodeName.bytes.val.map U8.toUInt8).map UInt8.toNat =
    [195, 169, 229, 173, 151, 230, 174, 181, 240, 159, 166, 128, 0] := rfl

/-- Iteration is over decoded Unicode scalar values, never over individual bytes. -/
theorem unicode_first_two : string_chars.first_two unicodeName =
    RustM.ok (some (Char.ofNat 233), some (Char.ofNat 23383)) := by
  have hs : unicodeName.toString.toList =
      [Char.ofNat 233, Char.ofNat 23383, Char.ofNat 27573, Char.ofNat 129408,
        Char.ofNat 0] := by
    rw [unicode_original_observation]
    change (String.ofList _).toList = _
    exact String.toList_ofList
  simp [string_chars.first_two, core.str.Str.chars, hs, core.str.iter.IteratorChars.next]

/-- Standard UTF-8 validation excludes continuation bytes, overlong encodings,
    surrogate encodings, values above U+10FFFF, and incomplete sequences. -/
theorem invalid_utf8_examples :
    ¬ (([128] : List UInt8).toByteArray.IsValidUTF8) ∧
    ¬ (([192, 128] : List UInt8).toByteArray.IsValidUTF8) ∧
    ¬ (([237, 160, 128] : List UInt8).toByteArray.IsValidUTF8) ∧
    ¬ (([244, 144, 128, 128] : List UInt8).toByteArray.IsValidUTF8) ∧
    ¬ (([226, 130] : List UInt8).toByteArray.IsValidUTF8) := by decide

theorem invalid_bytes_uninhabited : ¬ ∃ s : Str, s.bytes.val = [128#u8] := by
  rintro ⟨s, h⟩
  have hv := s.isValidUTF8
  rw [h] at hv
  exact invalid_utf8_examples.1 hv

end str_bytes
