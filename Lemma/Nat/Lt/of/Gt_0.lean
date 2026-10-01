import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x y : ℝ}
-- given
  (h : y - x > 0) :
-- imply
  x < y := by
-- proof
  exact sub_pos.mp h


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x - y > 0) :
-- imply
  y < x := by
-- proof
  exact sub_pos.mp h


@[main]
private lemma scale
  {x t : ℝ}
-- given
  (ht : t < 1)
  (h : x > 0) :
-- imply
  t * x < x := by
-- proof
  nlinarith


-- created on 2026-09-27
