import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (r : Fin m → ℕ) (i j : RothMvIndex m) :
-- imply
  rothMvWeight r (i + j) = rothMvWeight r i + rothMvWeight r j := by
-- proof
  simp only [rothMvWeight, Finsupp.add_apply, Nat.cast_add, add_div,
    Finset.sum_add_distrib]


-- created on 2026-10-21
