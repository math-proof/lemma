import sympy.Basic
import sympy.stats.stochastic_process_types
open scoped Matrix BigOperators


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {x0 : S → ℝ} [StochasticVec x0]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (n : ℕ) :
-- imply
  StochasticVec (cesaro_average x0 P n) := by
-- proof
  constructor
  ·
    intro i
    simp only [cesaro_average, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    apply mul_nonneg
    · positivity
    ·
      apply Finset.sum_nonneg
      intro k _
      apply (svec_mul_smat_is_svec _ _).nonneg
  ·
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (n + 1 : ℝ)⁻¹ * ∑ i, (x0 ᵥ* P ^ k) i := by
        simp only [cesaro_average, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ← Finset.mul_sum]
        rw [Finset.sum_comm]
      _ = ∑ k ∈ Finset.range (n + 1), (n + 1 : ℝ)⁻¹ * 1 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [(svec_mul_smat_is_svec _ _).rowsum]
      _ = (n + 1 : ℝ) * (n + 1 : ℝ)⁻¹ := by
        simp [Finset.sum_const]
      _ = 1 := by
        field_simp


-- created on 2026-09-22
-- updated on 2026-09-23
