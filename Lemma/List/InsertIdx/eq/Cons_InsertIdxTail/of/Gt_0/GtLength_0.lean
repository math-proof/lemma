import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h_s : s.length > 0)
  (h_d : d > 0)
  (x : α) :
-- imply
  s.insertIdx d x = s[0] :: s.tail.insertIdx (d - 1) x := by
-- proof
  conv_lhs => rw [← EqCons_Tail.of.GtLength_0 h_s]
  rw [InsertIdxCons.eq.Cons_InsertIdx.of.Gt_0 h_d]


-- created on 2026-07-14
