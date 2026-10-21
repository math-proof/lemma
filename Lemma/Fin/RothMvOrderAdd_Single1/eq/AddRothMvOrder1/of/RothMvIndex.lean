import Mathlib
import Lemma.Fin.EqRothMvOrder_Single
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvOrder_add_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (i : RothMvIndex m) (h : Fin m) :
-- imply
  rothMvOrder (i + Finsupp.single h 1) = rothMvOrder i + 1 := by
-- proof
  have rothMvOrder_add (i j : RothMvIndex m) :
    rothMvOrder (i + j) = rothMvOrder i + rothMvOrder j := by
    simp [rothMvOrder, Finset.sum_add_distrib]
  rw [rothMvOrder_add, EqRothMvOrder_Single]


-- created on 2026-10-21
