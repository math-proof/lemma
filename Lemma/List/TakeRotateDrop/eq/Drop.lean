import Lemma.List.TakeRotate.eq.Drop.of.EqLength_Add
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  ((s.drop i).rotate 1).take (s.length - 1 - i) = s.drop (i + 1) := by
-- proof
  rw [TakeRotate.eq.Drop.of.EqLength_Add (by grind)]
  simp


-- created on 2025-10-23
