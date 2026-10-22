import StrBytesProofs
import Lean.Util.CollectAxioms

/- Audit programs as well as proofs, including their generated proof auxiliaries.
   This is an environment check, not a native-evaluation proof certificate. -/
run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let prefixes : Array Lean.Name :=
    #[`str_bytes, `str_equality, `string_chars.first_two, `string_chars.collect,
      `Aeneas.Std.Str, `Aeneas.Std.instDecidableEqStr,
      `Aeneas.Std.U8.toUInt8, `Aeneas.Std.U8.ofUInt8, `Aeneas.Std.ByteArray,
      `Aeneas.Std.toStr, `Aeneas.Std.core.str]
  let env ← Lean.getEnv
  let decls := (env.constants.toList.map Prod.fst).filter (fun n =>
    prefixes.any (fun p => p.isPrefixOf n))
  decls.forM (fun n => do
    let used ← Lean.collectAxioms n
    used.forM (fun ax => do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} in {n}"))
  Lean.logInfo m!"UTF-8 program/proof axiom audit: {decls.length} declarations checked"

#print axioms str_bytes.literal_checks
#print axioms str_equality.literal_checks
#print axioms str_bytes.literal_checks_eq
#print axioms str_bytes.equality_literal_checks_eq
#print axioms str_bytes.original_string
#print axioms Aeneas.Std.Str.toString_injective
