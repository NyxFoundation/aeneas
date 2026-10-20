import Static

open Aeneas Aeneas.Std

namespace static

theorem nested_static_width :
    declaration_width (.Vector (.Vector .Boolean 2#usize) 4#usize) = RustM.ok (some 8#usize) := by
  cases System.Platform.numBits_eq <;>
    simp_all [declaration_width, Usize.checked_mul, core.num.checked_mul_UScalar,
      Option.ofRustM, UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds]

theorem nested_static_valid :
    declaration_valid (.Vector (.Vector .Boolean 2#usize) 4#usize) = RustM.ok (.Ok ()) := by
  simp [declaration_valid]

theorem empty_static_invalid (element : Declaration) :
    declaration_valid (.Vector element 0#usize) = RustM.ok (.Err ()) := by
  simp [declaration_valid]

end static
