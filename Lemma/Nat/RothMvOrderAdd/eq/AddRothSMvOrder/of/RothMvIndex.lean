import Mathlib
import sympy.Basic


/--
[rothMvOrder_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (i j : Finsupp (Fin m) ℕ) :
-- imply
  (∑ h : Fin m, (i + j) h) = (∑ h : Fin m, i h) + (∑ h : Fin m, j h) := by
-- proof
  simp [Finset.sum_add_distrib]


-- created on 2026-10-21
