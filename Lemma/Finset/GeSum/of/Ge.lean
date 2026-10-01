import sympy.Basic


@[main]
private lemma main
  {s : Finset ι}
  {f g : ι → ℝ}
-- given
  (h : ∀ i, f i ≥ g i) :
-- imply
  ∑ i ∈ s, f i ≥ ∑ i ∈ s, g i :=
-- proof
  Finset.sum_le_sum fun i _ => h i


-- created on 2019-06-01
