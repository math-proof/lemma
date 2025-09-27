import Lemma.Algebra.NotGe.is.Lt
import Lemma.Algebra.Le.of.Lt
open Algebra


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
  -- Case 1: x ≥ 0
  -- By the definition of absolute value, |x| = x when x ≥ 0
  ·
    apply abs_of_nonneg h
  -- Case 2: x < 0
  -- By the definition of absolute value, |x| = -x when x < 0
  ·
    have := Lt.of.NotGe h
    simp [abs_of_neg]
    apply Le.of.Lt this


-- created on 2025-04-11
-- updated on 2025-04-18
