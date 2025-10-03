import Lemma.List.TailCons.eq.Tail
import Lemma.List.IsConstant.of.All_Eq
open List


@[main]
private lemma main
  {s : List α}
-- given
  (h: s is constant) :
-- imply
  s.tail is constant := by
-- proof
  match s with
  | .nil =>
    simp [IsConstant.is_constant]
  | .cons x0 X =>
    simp [IsConstant.is_constant] at h
    apply IsConstant.of.All_Eq h


-- created on 2024-07-01
