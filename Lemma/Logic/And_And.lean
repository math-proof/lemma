import Lemma.Basic


@[main]
private lemma Comm :
-- imply
  p ∧ q ∧ r ↔ p ∧ r ∧ q := by
-- proof
  -- Use the constructor tactic to split the equivalence into two implications.
  constructor <;>
    intro h
  ·
    rw [And.comm (b := q)]
    assumption
  ·
    rw [And.comm (a := q)]
    assumption


-- created on 2025-06-06
