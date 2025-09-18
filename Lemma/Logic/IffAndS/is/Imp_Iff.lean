import Lemma.Basic


@[main]
private lemma main
-- given
  (p q r : Prop) :
-- imply
  (r ∧ p ↔ r ∧ q) ↔ (r → (p ↔ q)) := by
-- proof
  aesop

-- created on 2025-08-03
