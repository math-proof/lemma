import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import sympy.Basic
open Real Finset Filter


@[main]
private lemma main
  {ν : ℝ}
  {n₀ : ℕ}
-- given
  (h₀ : ν ≤ 1)
  (h₁ : 1 ≤ n₀) :
-- imply
  Tendsto (fun n => ∑ k ∈ range n, ((k : ℝ) + n₀) ^ (-ν)) atTop atTop := by
-- proof
  have hn₀ : (1 : ℝ) ≤ n₀ := by exact_mod_cast h₁
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop (inv_pos.2 (by linarith : (0 : ℝ) < n₀)))
  rw [mul_sum]
  refine sum_le_sum fun k _ => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc
    _ = ((n₀ : ℝ) * (k + 1))⁻¹ := by rw [mul_inv, one_div]
    _ ≤ ((k : ℝ) + n₀)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
    _ = ((k : ℝ) + n₀) ^ (-1 : ℝ) := (rpow_neg_one _).symm
    _ ≤ _ := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)


-- created on 2026-09-26