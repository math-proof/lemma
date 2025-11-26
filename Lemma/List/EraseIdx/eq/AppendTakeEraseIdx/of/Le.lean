import Lemma.List.DropEraseIdx.eq.Drop.of.Le
import Lemma.List.EqAppendTake__Drop
import Lemma.List.EqTake.of.LeLength
import Lemma.List.TakeAppend.eq.Take.of.GeLength
import Lemma.List.TakeTake.eq.Take.of.Ge
open List


@[main]
private lemma main
-- given
  (h : i ≤ d)
  (s : List α) :
-- imply
  s.eraseIdx i = (s.eraseIdx i).take d ++ s.drop (d + 1) := by
-- proof
  if h_d : d ≤ (s.eraseIdx i).length then
    rw [← EqAppendTake__Drop (s.eraseIdx i) d]
    simp [DropEraseIdx.eq.Drop.of.Le h]
    rw [TakeAppend.eq.Take.of.GeLength (by simpa)]
    rw [TakeTake.eq.Take.of.Ge (by simp)]
  else
    simp at h_d
    rw [EqTake.of.LeLength (by omega)]
    simp
    grind


-- created on 2025-11-03
