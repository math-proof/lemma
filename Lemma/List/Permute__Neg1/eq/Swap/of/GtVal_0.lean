import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h_i : i.val > 0) :
-- imply
  s.permute i (-1) = s.swap (i - 1) i := by
-- proof
  have := Swap.eq.Permute__Neg1.of.GtLength (s := s) (i := i - 1) (by grind)
  grind


-- created on 2026-07-11
