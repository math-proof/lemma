import sympy.vector.functions
import Lemma.Vector.SumDiv.eq.DivSum
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Vector.GtSumExp_0
open Vector Algebra


@[main]
private lemma main
  [ExpPos α]
  [NeZero n]
-- given
  (x : List.Vector α n) :
-- imply
  (x.softmax).sum = 1 := by
-- proof
  unfold List.Vector.softmax
  simp
  rw [SumDiv.eq.DivSum]
  rw [Div.eq.One.of.Gt_0]
  apply GtSumExp_0


-- created on 2025-10-07
