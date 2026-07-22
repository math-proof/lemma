import Lemma.Vector.Head.eq.Get_0
import Lemma.Vector.Sum.eq.Head
open Vector


@[main]
private lemma main
  [AddZeroClass α]
-- given
  (h : n = 1)
  (v : List.Vector α n) :
-- imply
  v.sum = v[0] := by
-- proof
  subst h
  rw [Get_0.eq.Head]
  apply Sum.eq.Head


-- created on 2026-07-22
