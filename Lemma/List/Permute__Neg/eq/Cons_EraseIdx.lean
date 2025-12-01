import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetPermute__Neg.eq.Get
import Lemma.List.TailPermute__Neg.eq.EraseIdx
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (d : Fin s.length) :
-- imply
  s.permute d (-d) = s[d] :: s.eraseIdx d := by
-- proof
  have h_d := d.isLt
  have := Eq_Cons_Tail.of.GtLength_0 (by simp; grind) (s := s.permute d (-d))
  rw [← TailPermute__Neg.eq.EraseIdx, this]
  simp
  apply GetPermute__Neg.eq.Get


-- created on 2025-12-01
