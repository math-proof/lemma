import sympy.sets.sets
import sympy.Basic


@[main]
private lemma relax.given
  {x y l : ℝ}
-- given
  (hl : l ≤ x)
  (h : l > y) :
-- imply
  x > y := by
-- proof
  exact lt_of_lt_of_le h hl


@[main]
private lemma transport.given
  {x y a : ℝ}
-- given
  (h : x > y - a) :
-- imply
  x + a > y := by
-- proof
  linarith


@[main]
private lemma transport
  {x y a : ℝ}
-- given
  (h : x + a > y) :
-- imply
  x > y - a := by
-- proof
  linarith


-- created on 2019-07-16
