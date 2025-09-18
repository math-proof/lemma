import Lemma.Basic


@[main]
private lemma Comm
  [AddCommMonoid β]
-- given
  (s : Finset γ)
  (t : Finset α)
  (f : γ → α → β) :
-- imply
  ∑ i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, ∑ i ∈ s, f i j := by
-- proof
  apply Finset.sum_comm


-- created on 2025-07-19
