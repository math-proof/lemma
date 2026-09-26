import sympy.stats.stochastic_process_types
import sympy.stats.stochastic_process
open WithLp
open scoped Matrix


@[main]
private lemma main
  {S : Type*} [Fintype S]
  {Q : Matrix S S ℝ}
-- given
  (hQ : RowStochastic Q)
  (x y : S → ℝ) :
-- imply
  ‖ofL1 (x ᵥ* Q - y ᵥ* Q)‖ ≤ ‖ofL1 (x - y)‖ := by
-- proof
  have hxy : ∀ j, (x ᵥ* Q - y ᵥ* Q) j = ∑ i, (x i - y i) * Q i j := by
    intro j
    change (x ᵥ* Q) j - (y ᵥ* Q) j = _
    simp [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib]
  have hleft : ‖ofL1 (x ᵥ* Q - y ᵥ* Q)‖ = ∑ j, |(x ᵥ* Q - y ᵥ* Q) j| := by
    simpa [ofL1] using (PiLp.norm_eq_sum (f := ofL1 (x ᵥ* Q - y ᵥ* Q)))
  have hright : ‖ofL1 (x - y)‖ = ∑ i, |(x - y) i| := by
    simpa [ofL1] using (PiLp.norm_eq_sum (f := ofL1 (x - y)))
  rw [hleft, hright]
  calc
      ∑ j, |(x ᵥ* Q - y ᵥ* Q) j|
    _ = ∑ j, |∑ i, (x i - y i) * Q i j| := by
        apply Finset.sum_congr rfl; intro j _; rw [hxy]
    _ ≤ ∑ j, ∑ i, |(x i - y i) * Q i j| := by
        apply Finset.sum_le_sum; intro j _; exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ i, |x i - y i| * Q i j := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro i _
        rw [abs_mul, abs_of_nonneg ((hQ.stochastic i).nonneg j)]
    _ = ∑ i, ∑ j, |x i - y i| * Q i j := by rw [Finset.sum_comm]
    _ = ∑ i, |x i - y i| * ∑ j, Q i j := by
        apply Finset.sum_congr rfl; intro i _; rw [← Finset.mul_sum]
    _ = ∑ i, |x i - y i| := by
        apply Finset.sum_congr rfl; intro i _; rw [(hQ.stochastic i).rowsum, mul_one]
    _ = ∑ i, |(x - y) i| := by
        apply Finset.sum_congr rfl; intro i _; rfl


-- created on 2026-09-19
