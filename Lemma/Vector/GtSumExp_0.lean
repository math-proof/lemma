import sympy.vector.functions
import Lemma.Vector.Sum.eq.Sum_Get
open Vector


@[main]
private lemma main
  [ExpPos α]
  [NeZero n]
-- given
  (x : List.Vector α n) :
-- imply
  (exp x).sum > 0 := by
-- proof
  rw [Sum.eq.Sum_Get]
  sorry


-- created on 2025-10-07
