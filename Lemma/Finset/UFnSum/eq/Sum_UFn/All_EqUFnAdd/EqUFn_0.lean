import sympy.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [AddCommMonoid N]
  [AddCommMonoid N']
  {f : N → N'}
-- given
  (h₀ : f 0 = 0)
  (h₁ : ∀ a b, f (a + b) = f a + f b)
  (s : Finset ι)
  (x : ι → N):
-- imply
  f (∑ i ∈ s, x i) = ∑ i ∈ s, f (x i) := by
-- proof
  induction s using Finset.induction_on with
  -- apply Finset.induction_on (motive := fun s => f (∑ i ∈ s, x i) = ∑ i ∈ s, f (x i)) s
  | empty =>
    simp_all
  | insert j s hj ih =>
    simp [Finset.sum_insert hj]
    simp_all


-- created on 2025-07-14
