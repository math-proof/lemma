import sympy.Basic


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
  induction s using Finset.induction_on with
  -- apply Finset.induction_on (motive := fun s => f (∏ i ∈ s, x i) = ∏ i ∈ s, f (x i)) s
  | empty =>
    simp_all
  | insert j s hj ih =>
    simp_all [Finset.prod_insert hj]

-- created on 2025-07-22
