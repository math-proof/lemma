import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.Corollary_1_43_6
open FusionRing


/--
[Corollary_1_43_6](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_43_6.lean)
-/
@[path]
private lemma Corollary_1_43_6_eq
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i : ι} :
-- imply
  ∃ n : ℕ, 0 < n ∧ 0 < (R.grTraceC (grPowC R (basisVecC i) n)).re := by
-- proof
  apply Corollary_1_43_6 R i


-- created on 2026-10-23
