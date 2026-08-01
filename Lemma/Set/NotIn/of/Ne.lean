import sympy.Basic


@[main]
private lemma main
  {x y : α}
-- given
  (h : x ≠ y) :
-- imply
  x ∉ ({y} : Set α) := by
-- proof
  -- Use the `simp` tactic to simplify the membership condition.
  -- This tactic knows that the only element in `{y}` is `y`, so `x ∈ {y}` simplifies to `x = y`.
  -- Given the hypothesis `h : x ≠ y`, this leads to a contradiction.
  simp [h]


-- created on 2018-03-08
