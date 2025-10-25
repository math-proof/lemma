import sympy.Basic


@[main]
private lemma main
-- given
  (s : Finset ι)
  (f g : ι → ℝ) :
-- imply
  ∑ i ∈ s, f i * g i ≤ √(∑ i ∈ s, f i ^ 2) * √(∑ i ∈ s, g i ^ 2) :=
-- proof
  Real.sum_mul_le_sqrt_mul_sqrt s f g


-- created on 2025-04-06
