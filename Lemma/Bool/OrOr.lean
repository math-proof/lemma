import sympy.Basic


@[main]
private lemma Comm :
-- imply
  (p ∨ q) ∨ r ↔ (q ∨ p) ∨ r := by
-- proof
  -- Use the commutativity of OR (or_comm) to swap p and q in the first disjunct.
  simp [or_comm]


-- created on 2025-06-06
