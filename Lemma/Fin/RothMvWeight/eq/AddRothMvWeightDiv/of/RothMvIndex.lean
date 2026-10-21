import Mathlib
import Lemma.Fin.EqRothLastIndex_Last.of.RothMvIndex
import Lemma.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvWeight_lastIndex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
-- given
  (r : Fin (n + 1) → ℕ)
  (i : RothMvIndex n)
  (a : ℕ) :
-- imply
  rothMvWeight r (rothLastIndex i a) =
    rothMvWeight (fun h ↦ r h.castSucc) i + (a : ℝ) / r (Fin.last n) := by
-- proof
  unfold rothMvWeight
  rw [Fin.sum_univ_castSucc]
  simp only [EqRothLastIndexCastSucc.of.RothMvIndex, EqRothLastIndex_Last.of.RothMvIndex]


-- created on 2026-10-21
