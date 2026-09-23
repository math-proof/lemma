import Lemma.Matrix.VecMulSum.eq.Sum_VecMul
import Lemma.Matrix.VecMulSMul.eq.SMul_VecMul
import Lemma.Matrix.L1Norm.eq.One.of.StochasticVec
import Lemma.Matrix.OfL1.eq.Sub
import Lemma.Matrix.OfL1.eq.SMul
open WithLp Matrix
open scoped Matrix BigOperators


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S]
  {x0 : S → ℝ} [StochasticVec x0]
  {P : Matrix S S ℝ} [RowStochastic P]
-- given
  (n : ℕ) :
-- imply
  ‖ofL1 (cesaro_average x0 P n ᵥ* P - cesaro_average x0 P n)‖ ≤
    2 / (n + 1) := by
-- proof
  set c : ℝ := (n + 1 : ℝ)⁻¹
  have hcpos : 0 < c := by unfold c; positivity
  set sk : S → ℝ := ∑ k ∈ Finset.range (n + 1), x0 ᵥ* P ^ k
  have havg : cesaro_average x0 P n = c • sk := rfl
  have hlin : (c • sk) ᵥ* P - c • sk = c • (sk ᵥ* P - sk) := by
    simp [sub_eq_add_neg, Matrix.VecMulSMul.eq.SMul_VecMul, smul_add, smul_neg]
  have hskP : sk ᵥ* P = ∑ k ∈ Finset.range (n + 1), x0 ᵥ* P ^ (k + 1) := by
    simp only [sk]
    rw [Matrix.VecMulSum.eq.Sum_VecMul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.vecMul_vecMul, ← pow_succ]
  have htel : sk ᵥ* P - sk = x0 ᵥ* P ^ (n + 1) - x0 := by
    rw [hskP, ← Finset.sum_sub_distrib]
    simpa [pow_zero, Matrix.vecMul_one] using
      Finset.sum_range_sub (fun k => x0 ᵥ* P ^ k) (n + 1)
  rw [havg, hlin, htel, Matrix.OfL1.eq.SMul, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  calc
    _ = c * ‖ofL1 (x0 ᵥ* P ^ (n + 1) - x0)‖ := rfl
    _ ≤ c * 2 := by
      apply mul_le_mul_of_nonneg_left _ hcpos.le
      rw [Matrix.OfL1.eq.Sub]
      rw [← show (1 : ℝ) + 1 = 2 by ring]
      apply le_trans (norm_sub_le _ _)
      apply add_le_add <;>
      · exact Matrix.L1Norm.eq.One.of.StochasticVec.le
    _ = 2 / (n + 1) := by unfold c; field_simp


-- created on 2026-09-22
