import sympy.Basic
import sympy.vector.functions


@[main]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n) :
-- imply
  x.sigmoid = 1 / (1 + exp (-x)) := by
-- proof
  unfold List.Vector.sigmoid
  rfl


-- created on 2026-07-05
