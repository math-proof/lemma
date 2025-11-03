import Lemma.List.EraseIdx.eq.AppendTakeEraseIdx.of.Le
import Lemma.List.TakeEraseIdx.eq.EraseIdxTake.of.Ge
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main]
private lemma main
-- given
  (h : i < d)
  (s : List α) :
-- imply
  s.eraseIdx i = (s.take d).eraseIdx i ++ s.drop d := by
-- proof
  rw [EraseIdx.eq.AppendTakeEraseIdx.of.Le (by omega) (d := d - 1)]
  rw [EqAddSub.of.Ge (by omega)]
  rw [TakeEraseIdx.eq.EraseIdxTake.of.Ge (by omega)]
  rw [EqAddSub.of.Ge (by omega)]


-- created on 2025-11-03
