import stdlib.List
import Lemma.List.DropRotate.eq.Take.of.Le_Length
import Lemma.Nat.Ge.of.Eq_Add
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length = n + m) :
-- imply
  (s.rotate n).drop m = s.take n := by
-- proof
  convert DropRotate.eq.Take.of.Le_Length (Ge.of.Eq_Add h)
  simp [h]


-- created on 2025-10-22
