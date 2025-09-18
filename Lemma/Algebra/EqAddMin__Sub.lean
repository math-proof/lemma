import Lemma.Basic


@[main]
private lemma main
-- given
  (a b : ℕ) :
-- imply
  a ⊓ b + (a - b) = a := by
-- proof
  obtain h | h := le_total a b <;>
    simp [h]


-- created on 2025-06-07
