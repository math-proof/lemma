import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.ShiftedRiordanArrayRowSums
open MetaMathlibExt


/--
[shiftedRiordanArray_constantTerm_and_sumCoefficients](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ShiftedRiordanArrayRowSums.lean)
-/
@[path]
private lemma shiftedRiordanArray_constantTerm_and_sumCoefficients_eq
  [CommSemiring R]
  {A : ℕ → ℕ → R}
  {r : R}
  {n : ℕ} :
-- imply
  let shifted : R → ℕ → ℕ → R := by
-- proof
  apply MetaMathlibExt.shiftedRiordanArray_constantTerm_and_sumCoefficients A r n


-- created on 2026-10-20
