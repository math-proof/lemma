import Lemma.Basic


@[main, comm]
private lemma main
  [DecidableEq ι]
  [CommMonoid α]
  {s : Finset ι}
  {a b : ι → α} :
-- imply
  ∏ i ∈ s, a i * b i = (∏ i ∈ s, a i) * ∏ i ∈ s, b i := by
-- proof
  apply Finset.induction_on (p := fun s => ∏ i ∈ s, a i * b i = (∏ i ∈ s, a i) * ∏ i ∈ s, b i) s
  ·
    simp
  ·
    intro j s hj ih
    simp [Finset.prod_insert hj]
    simp_all [mul_assoc, mul_left_comm]


-- created on 2025-04-27
