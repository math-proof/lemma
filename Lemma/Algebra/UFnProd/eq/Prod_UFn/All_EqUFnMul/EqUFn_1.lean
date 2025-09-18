import Lemma.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [CommMonoid α]
  [CommMonoid β]
  {f : α → β}
-- given
  (h₀ : f 1 = 1)
  (h₁ : ∀ a b, f (a * b) = f a * f b)
  (s : Finset ι)
  (x : ι → α) :
-- imply
  f (∏ i ∈ s, x i) = ∏ i ∈ s, f (x i) := by
-- proof
  apply Finset.induction_on (p := fun s => f (∏ i ∈ s, x i) = ∏ i ∈ s, f (x i)) s
  ·
    simp_all
  ·
    intro j s hj ih
    simp [Finset.prod_insert hj]
    simp_all


-- created on 2025-07-22
