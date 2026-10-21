import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (r : Fin m → ℕ) (i : RothMvIndex m) :
-- imply
  0 ≤ rothMvWeight r i := by
-- proof
  unfold rothMvWeight
  positivity


-- created on 2026-10-21
