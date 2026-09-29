import sympy.sets.sets
import sympy.Basic


@[main]
private lemma simp.terms.negative
  {x y a b : ℝ}
-- given
  (h : x - a ≤ y - b) :
-- imply
  x + b ≤ y + a := by
-- proof
  linarith


@[main]
private lemma transport
  {x y a : ℝ}
-- given
  (h : x + a ≤ y) :
-- imply
  x ≤ y - a := by
-- proof
  linarith


-- created on 2026-09-27
