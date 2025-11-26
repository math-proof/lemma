import Lemma.List.DropRotate.eq.Take.of.GeLength
import Lemma.Nat.Le.of.EqAdd
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length = n + m) :
-- imply
  (s.rotate n).drop m = s.take n := by
-- proof
  have := Ge.of.Eq_Add h
  convert DropRotate.eq.Take.of.GeLength this
  simp [h]


-- created on 2025-10-22
