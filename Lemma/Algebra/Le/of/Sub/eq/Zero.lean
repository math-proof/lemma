import sympy.Basic


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x - y = 0) :
-- imply
  x ≤ y := by
-- proof
  -- Use the `omega` tactic to solve the inequality based on the given equation `x - y = 0`.
  -- The `omega` tactic is a decision procedure for linear arithmetic over the natural numbers.
  omega


-- created on 2025-04-11
