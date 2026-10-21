import Aeneas.Std.Scalar
import Aeneas.Std.Slice
import Aeneas.Std.StringDef

namespace Aeneas.Std

instance : DecidableEq Str := inferInstanceAs (DecidableEq (Slice U8))

/-- Shared byte view. `Str` is represented by its UTF-8 bytes, not by characters.
    The Rust signature ties the returned shared slice to the input lifetime;
    the ordinary builtin-call interpreter retains that dependency. -/
@[rust_fun "core::str::{str}::as_bytes"]
def core.str.Str.as_bytes (s : Str) : RustM (Slice U8) := .ok s

@[simp, step_simps]
theorem core.str.Str.as_bytes_eq (s : Str) : as_bytes s = .ok s := rfl

/-- Exact list equality preserves every byte and its order, for arbitrary inputs. -/
theorem core.str.Str.as_bytes_exact (s : Str) :
    ∃ bs, as_bytes s = .ok bs ∧ bs.val = s.val ∧ bs.val.length = s.val.length ∧
      ∀ i : Nat, bs.val[i]? = s.val[i]? :=
  ⟨s, rfl, rfl, rfl, fun _ => rfl⟩

/-- `bs.toList` has the same length as `bs`. -/
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

/-- TODO: we shouldn't use `decide +native` but it seems we can't reduce it otherwise. -/
def toStr (s : String) (h : s.toByteArray.size ≤ U32.max := by decide +native) : Str :=
  ⟨ s.toByteArray.toList.map
    (fun x => ⟨ x.toNat, by cases x; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega  ⟩),
    by
      simp only [UScalarTy.U8_numBits_eq, Nat.reducePow, Fin.mk_uInt8ToNat, BitVec.ofFin_uInt8ToFin,
        List.length_map]
      rw [ByteArray.length_toList]
      exact h.trans (by scalar_tac) ⟩

/-- The string conversion preserves the UTF-8 encoder's bytes and their order.
    The size premise is explicit: this proof does not use native evaluation. -/
theorem toStr_utf8_bytes (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val.map (fun b => b.val) = s.toByteArray.toList.map UInt8.toNat := by
  simp only [toStr, List.map_map]
  congr 1

theorem toStr_utf8_length (s : String) (h : s.toByteArray.size ≤ U32.max) :
    (toStr s h).val.length = s.toByteArray.size := by
  simp only [toStr, List.length_map, ByteArray.length_toList]

example : Str := toStr "hello"

end Aeneas.Std
