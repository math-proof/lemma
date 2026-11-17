module

public import Mathlib
public import Theorem.Fin.EqRothLastIndex_Last.of.RothMvIndex
public import Theorem.Fin.EqRothLastIndexCastSucc.of.RothMvIndex

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothMvWeight_lastIndex](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvWeight.eq.AddRothMvWeightDiv.of.RothMvIndex
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
