import sympy.Basic


@[main]
private lemma Comm :
-- imply
  p ∧ q ∧ r ↔ p ∧ r ∧ q := by
-- proof
  -- Use the constructor tactic to split the equivalence into two implications.
  constructor <;>
    intro h
  ·
    rwa [And.comm (b := q)]
  ·
    rwa [And.comm (a := q)]


-- created on 2025-06-06
