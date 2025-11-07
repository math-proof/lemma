import Lemma.List.EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.Succ.eq.Add_1
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > 0)
  (h_i : i > 0) :
-- imply
  s[0] :: s.tail.eraseIdx (i - 1) = s.eraseIdx i := by
-- proof
  rw [← EraseIdx.eq.Cons_EraseIdxTail.of.GtLength_0 h]
  rw [Succ.eq.Add_1]
  rw [EqAddSub.of.Ge (by omega)]


@[main]
private lemma headD
  {s : List α}
-- given
  (h : s.length > 0)
  (h_i : i > 0)
  (default : α) :
-- imply
  s.headD default :: s.tail.eraseIdx (i - 1) = s.eraseIdx i := by
-- proof
  rw [HeadD.eq.Get_0.of.GtLength_0 h]
  apply main h h_i


-- created on 2025-11-07
