import Lemma.Basic


@[main]
private lemma MAIN
  {p q r : Prop} :
-- imply
  p ∧ ¬(q ∧ ¬r) ↔ p ∧ q ∧ r ∨ p ∧ ¬q := by
-- proof
  -- Simplify the left-hand side using De Morgan's Law and double negation
  simp [not_and]
  -- Use tauto to handle the logical equivalence and conclude the proof
  tauto


-- created on 2025-04-09
