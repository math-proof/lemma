import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvOrder_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (h : Fin m) (n : ℕ) :
-- imply
  rothMvOrder (Finsupp.single h n) = n := by
-- proof
  simp [rothMvOrder]


-- created on 2026-10-21
