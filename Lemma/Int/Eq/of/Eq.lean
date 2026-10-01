import sympy.sets.sets
import sympy.Basic


@[main]
private lemma transport.given
  {x y a : ℝ}
-- given
  (h : x = y - a) :
-- imply
  x + a = y := by
-- proof
  rw [h]
  ring


-- created on 2022-04-01
