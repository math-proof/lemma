import sympy.vector.functions
import Lemma.Vector.SumDiv.eq.DivSum
open Vector


@[main]
private lemma main
  [ExpPos α]
-- given
  (x : List.Vector α n) :
-- imply
  (x.softmax).sum = 1 := by
-- proof
  unfold List.Vector.softmax
  simp
  rw [SumDiv.eq.DivSum]
  sorry


-- created on 2025-10-07
