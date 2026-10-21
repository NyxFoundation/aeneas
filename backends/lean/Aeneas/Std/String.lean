import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.Std.StringDef

namespace Aeneas.Std

/-- Shared byte view; the normal Rust signature-driven interpreter retains loans. -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : RustM (Slice U8) := .ok s.bytes

@[simp, step_simps]
theorem core.str.Str.as_bytes_eq (s : Str) : as_bytes s = .ok s.bytes := rfl

/-- Exact byte, order, position and length preservation for arbitrary Rust strings. -/
theorem core.str.Str.as_bytes_exact (s : Str) :
    ∃ bs, as_bytes s = .ok bs ∧ bs.val = s.bytes.val ∧
      bs.val.length = s.bytes.val.length ∧ ∀ i : Nat, bs.val[i]? = s.bytes.val[i]? :=
  ⟨s.bytes, rfl, rfl, rfl, fun _ => rfl⟩

/-- `bs.toList` has the same length as `bs` (retained public byte-array law). -/
theorem ByteArray.length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  have loop_length :
      ∀ (i : Nat) (r : List UInt8), i ≤ bs.size →
        (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      have hi' : i + 1 ≤ bs.size := by scalar_tac
      rw [ih hi']
      simp; scalar_tac
    | case2 i r h =>
      simp; scalar_tac
  unfold ByteArray.toList
  rw [loop_length 0 [] (Nat.zero_le _)]
  simp

/-- Conversion of any native-sized Lean string. There is no U32 cap or native
    proof default. Extracted literals instead use `Str.ofBytes`. -/
def toStr (s : String) (h : s.toByteArray.size ≤ Usize.max) : Str :=
  { bytes := ⟨s.toByteArray.data.toList.map U8.ofUInt8, by simpa using h⟩
    isValidUTF8 := by simpa [List.map_map, Function.comp_def] using s.isValidUTF8 }

@[simp] theorem toStr_bytes (s : String) (h : s.toByteArray.size ≤ Usize.max) :
    (toStr s h).bytes.val.map U8.toUInt8 = s.toByteArray.data.toList := by
  simp [toStr, List.map_map, Function.comp_def]

@[simp] theorem toStr_length (s : String) (h : s.toByteArray.size ≤ Usize.max) :
    (toStr s h).bytes.val.length = s.toByteArray.size := by
  simp [toStr]

@[simp] theorem Str.toString_toStr (s : String) (h : s.toByteArray.size ≤ Usize.max) :
    (toStr s h).toString = s := by
  apply String.toByteArray_inj.mp
  simp

@[simp] theorem Str.toStr_toString (s : Str) :
    toStr s.toString (by simpa using s.bytes.property) = s := by
  cases s with
  | mk bytes valid =>
    apply Str.ext
    apply Subtype.ext
    simp [toStr, Str.toString, String.fromUTF8, List.map_map, Function.comp_def]

theorem Str.toString_injective : Function.Injective Str.toString := by
  intro a b h
  apply Str.ext
  apply Subtype.ext
  have hb := congrArg (fun s : String => s.toByteArray.data.toList.map U8.ofUInt8) h
  simpa [Str.toString, String.fromUTF8, List.map_map, Function.comp_def] using hb

end Aeneas.Std
