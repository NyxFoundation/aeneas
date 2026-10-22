import Aeneas.Std.Scalar.Core
import Aeneas.Std.SliceDef
import Init.Data.String.Basic

namespace Aeneas.Std

/-- Lossless conversion between the model's byte scalars and Lean's bytes. -/
def U8.toUInt8 (b : U8) : UInt8 := ⟨b.bv⟩
def U8.ofUInt8 (b : UInt8) : U8 := ⟨b.toBitVec⟩

@[simp] theorem U8.ofUInt8_toUInt8 (b : U8) : ofUInt8 (toUInt8 b) = b := rfl
@[simp] theorem U8.toUInt8_ofUInt8 (b : UInt8) : toUInt8 (ofUInt8 b) = b := rfl

@[simp] theorem ByteArray.toByteArray_data_toList (b : ByteArray) :
    b.data.toList.toByteArray = b := by
  apply ByteArray.ext
  simp

/-- Rust `str`: native-sized bytes with Rust's existing UTF-8 type invariant.
    Validity uses Lean's standard UTF-8 predicate, not a new character decoder. -/
structure Str where
  bytes : Slice U8
  isValidUTF8 : (bytes.val.map U8.toUInt8).toByteArray.IsValidUTF8

@[ext] theorem Str.ext {a b : Str} (h : a.bytes = b.bytes) : a = b := by
  cases a
  cases b
  cases h
  rfl

instance : DecidableEq Str := fun a b =>
  if h : a.bytes.val = b.bytes.val then
    isTrue (Str.ext (Subtype.ext h))
  else isFalse (fun heq => h (congrArg (fun s => s.bytes.val) heq))

namespace Str

/-- Literal construction exposes every byte; both obligations are kernel proofs. -/
def ofBytes (bs : List U8) (size : bs.length ≤ Usize.max)
    (valid : (bs.map U8.toUInt8).toByteArray.IsValidUTF8) : Str :=
  ⟨⟨bs, size⟩, valid⟩

/-- Total, faithful Unicode observation. No caller-side validity premise. -/
def toString (s : Str) : String :=
  String.fromUTF8 (s.bytes.val.map U8.toUInt8).toByteArray s.isValidUTF8

@[simp] theorem toString_bytes (s : Str) :
    s.toString.toByteArray = (s.bytes.val.map U8.toUInt8).toByteArray := rfl

@[simp] theorem toString_byte_list (s : Str) :
    s.toString.toByteArray.data.toList = s.bytes.val.map U8.toUInt8 := by simp

@[simp] theorem toString_length (s : Str) :
    s.toString.toByteArray.size = s.bytes.val.length := by simp

theorem toString_native_size (s : Str) :
    s.toString.toByteArray.size ≤ Usize.max := by simpa using s.bytes.property

end Str
end Aeneas.Std
