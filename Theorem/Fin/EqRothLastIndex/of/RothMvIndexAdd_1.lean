module

public import Mathlib
public import Theorem.Fin.EqRothLastIndex_Last.of.RothMvIndex
public import Theorem.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
public import Theorem.Fin.EqRothLastTail.of.RothMvIndexAdd_1

public section

open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastIndex_eta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.EqRothLastIndex.of.RothMvIndexAdd_1
  {n : ℕ}
-- given
  (d : RothMvIndex (n + 1)) :
-- imply
  rothLastIndex (rothLastTail d) (d (Fin.last n)) = d := by
-- proof
  ext h
  refine Fin.lastCases ?_ (fun j ↦ ?_) h
  · rw [EqRothLastIndex_Last.of.RothMvIndex]
  · rw [EqRothLastIndexCastSucc.of.RothMvIndex, EqRothLastTail.of.RothMvIndexAdd_1]


-- created on 2026-10-21
