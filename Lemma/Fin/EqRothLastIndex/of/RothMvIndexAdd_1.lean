import Mathlib
import Lemma.Fin.EqRothLastIndex_Last.of.RothMvIndex
import Lemma.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
import Lemma.Fin.EqRothLastTail.of.RothMvIndexAdd_1
open MathlibExt.NumberTheory.RothAuxiliary
open Fin


/--
[rothLastIndex_eta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
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
