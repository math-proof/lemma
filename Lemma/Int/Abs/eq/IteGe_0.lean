import Lemma.Nat.NotGe.is.Lt
import Lemma.Nat.Le.of.Lt
open Nat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α} :
-- imply
  |x| = if x ≥ 0 then
    x
  else
    -x := by
-- proof
  -- Split the proof into two cases based on the condition x ≥ 0
  split_ifs with h
  ·
    apply abs_of_nonneg h
  ·
    have := Lt.of.NotGe h
    simp
    apply Le.of.Lt this


-- created on 2025-04-11
-- updated on 2025-04-18
