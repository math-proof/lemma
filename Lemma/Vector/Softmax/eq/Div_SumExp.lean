import sympy.vector.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α] [Div α]
-- given
  (x : List.Vector α n) :
-- imply
  x.softmax = exp x / (exp x).sum := by
-- proof
  unfold List.Vector.softmax
  simp


-- created on 2025-10-03
