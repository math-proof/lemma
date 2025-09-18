import Lemma.Basic


@[main]
private lemma main
  [DecidableEq ι]
  [AddCommMonoid α]
  {s : Finset ι}
  {a b : ι → α} :
-- imply
  ∑ i ∈ s, (a i + b i) = ∑ i ∈ s, a i + ∑ i ∈ s, b i := by
-- proof
  apply Finset.induction_on (p := fun s => ∑ i ∈ s, (a i + b i) = ∑ i ∈ s, a i + ∑ i ∈ s, b i) s
  ·
    simp
  ·
    intro j s hj ih
    simp [Finset.sum_insert hj]
    simp_all [add_assoc, add_left_comm]


-- created on 2025-04-06
-- updated on 2025-04-27
