import Lemma.Basic


@[main]
private lemma main
-- given
  (s : Set α)
  (a : α)
  (p : α → Prop) :
-- imply
  (∀ ι ∈ (Set.insert a s), p ι) ↔ p a ∧ ∀ ι ∈ s, p ι := by
-- proof
  simp [Set.insert]


-- created on 2025-07-19
