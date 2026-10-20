import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DPRM
open scoped Dioph Vector3 Nat Function
open MathlibExt.NumberTheory.DPRMWanted


/--
[dprm_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DPRM.lean)
-/
@[path]
private lemma dprm_theorem_eq
  {S : Set ℕ} :
-- imply
  REPred (fun n => n ∈ S) ↔ Dioph {v : Unit → ℕ | v () ∈ S} := by
-- proof
  apply MathlibExt.NumberTheory.DPRMWanted.dprm_theorem S


-- created on 2026-10-20
