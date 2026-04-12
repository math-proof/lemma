import Lemma.List.Eq_Nil.is.EqLength_0
import Lemma.List.TakeRotate.eq.Drop.of.GeLength
open List


@[main, comm]
private lemma main
  {s : List α} :
-- imply
  (s.rotate 1).take (s.length - 1) = s.tail := by
-- proof
  if h : s.length > 0 then
    have := TakeRotate.eq.Drop.of.GeLength (by grind) (s := s) (n := 1)
    simp_all
  else
    have h : s.length = 0 := by omega
    simp [h]
    have h := Eq_Nil.of.EqLength_0 h
    grind


-- created on 2026-04-12
