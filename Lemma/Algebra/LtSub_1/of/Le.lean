import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
-- given
  (h : x ≤ y) :
-- imply
  x - 1 < y := by
-- proof
  -- Use the `linarith` tactic to solve the inequality involving integers.
  linarith


-- created on 2025-03-28
-- updated on 2025-05-03
