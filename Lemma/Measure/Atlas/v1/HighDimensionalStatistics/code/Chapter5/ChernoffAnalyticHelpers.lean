import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.ChernoffAnalyticHelpers
open Finset Real ChernoffHelpers


namespace ChernoffHelpers

/--
[binom_ratio_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma binom_ratio_ineq
  {n j k : ℕ}
-- given
  (hj : j + 1 ≤ k)
  (hk : k ≤ n) :
-- imply
  (n - k + 1) * (j + 1) ≤ (n - j) * k := by
-- proof
  have hjn : j ≤ n := le_trans (Nat.le_of_succ_le hj) hk
  zify [hk, hjn]; nlinarith

end ChernoffHelpers

namespace ChernoffHelpers

/--
[choose_step_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma choose_step_bound
  {n j k : ℕ}
-- given
  (hj : j + 1 ≤ k)
  (hk : k ≤ n) :
-- imply
  (n - k + 1) * Nat.choose n j ≤ k * Nat.choose n (j + 1) := by
-- proof
  have h := Nat.choose_succ_right_eq n j
  by_cases hcj : Nat.choose n j = 0
  · simp [hcj]
  · have hj1_pos : 0 < j + 1 := Nat.succ_pos j
    suffices (n - k + 1) * Nat.choose n j * (j + 1) ≤
      k * Nat.choose n (j + 1) * (j + 1) from
      Nat.le_of_mul_le_mul_right this hj1_pos
    calc (n - k + 1) * Nat.choose n j * (j + 1)
      = (n - k + 1) * (j + 1) * Nat.choose n j := by ring
      _ ≤ (n - j) * k * Nat.choose n j := by
        apply Nat.mul_le_mul_right; exact binom_ratio_ineq n j k hj hk
      _ = k * (Nat.choose n j * (n - j)) := by ring
      _ = k * (Nat.choose n (j + 1) * (j + 1)) := by rw [h]
      _ = k * Nat.choose n (j + 1) * (j + 1) := by ring

end ChernoffHelpers

namespace ChernoffHelpers

/--
[choose_iterated_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma choose_iterated_bound
  {n k t m : ℕ}
-- given
  (htm : t + m ≤ k)
  (hk : k ≤ n) :
-- imply
  (n - k + 1) ^ m * Nat.choose n t ≤ k ^ m * Nat.choose n (t + m) := by
-- proof
  induction m with
  | zero => simp
  | succ m ih =>
    have htm' : t + m + 1 ≤ k := by omega
    have htm_le : t + m ≤ k := by omega
    have hstep := choose_step_bound n (t + m) k htm' hk
    calc (n - k + 1) ^ (m + 1) * Nat.choose n t
      = (n - k + 1) * ((n - k + 1) ^ m * Nat.choose n t) := by ring
      _ ≤ (n - k + 1) * (k ^ m * Nat.choose n (t + m)) := by
        apply Nat.mul_le_mul_left; exact ih htm_le
      _ = k ^ m * ((n - k + 1) * Nat.choose n (t + m)) := by ring
      _ ≤ k ^ m * (k * Nat.choose n (t + m + 1)) := by
        apply Nat.mul_le_mul_left; exact hstep
      _ = k ^ (m + 1) * Nat.choose n (t + m + 1) := by ring

end ChernoffHelpers

namespace ChernoffHelpers

/--
[choose_ratio_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma choose_ratio_bound
  {n k t : ℕ}
-- given
  (ht : 2 * t ≤ k)
  (hk : k ≤ n) :
-- imply
  (n - k + 1) ^ (k - 2 * t) * Nat.choose n t ≤ k ^ (k - 2 * t) * Nat.choose n (k - t) := by
-- proof
  have hm : t + (k - 2 * t) = k - t := by omega
  rw [← hm]
  exact choose_iterated_bound n k t (k - 2 * t) (by omega) hk

end ChernoffHelpers

namespace ChernoffHelpers

/--
[vandermonde_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma vandermonde_decomposition
  {d k : ℕ}
-- given
  (hk : k ≤ d) :
-- imply
  Nat.choose d k = ∑ ij ∈ Finset.antidiagonal k, Nat.choose k ij.1 * Nat.choose (d - k) ij.2 := by
-- proof
  have h : d = k + (d - k) := (Nat.add_sub_cancel' hk).symm
  conv_lhs => rw [h]
  exact Nat.add_choose_eq k (d - k) k

end ChernoffHelpers

namespace ChernoffHelpers

/--
[power_ineq_for_chernoff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma power_ineq_for_chernoff
  {R : ℝ}
-- given
  (hR : R ≥ 4) :
-- imply
  (2 * (R - 1)) ^ 4 ≥ 1 + R := by
-- proof
  nlinarith [sq_nonneg (R - 4), sq_nonneg R, sq_nonneg (R - 1)]

end ChernoffHelpers

namespace ChernoffHelpers

/--
[log_ratio_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma log_ratio_bound
  {d k : ℝ}
-- given
  (hk : k ≥ 1)
  (hd : d ≥ 8 * k) :
-- imply
  k / 2 * Real.log ((d - 2 * k + 1) / k) ≥ k / 8 * Real.log (1 + d / (2 * k)) := by
-- proof
  have hk_pos : k > 0 := by linarith
  have hk2_pos : 2 * k > 0 := by linarith
  set R := d / (2 * k) with hR_def
  have hR : R ≥ 4 := by rw [hR_def, ge_iff_le, le_div_iff₀ hk2_pos]; linarith
  have h_ratio_lb : (d - 2 * k + 1) / k ≥ 2 * (R - 1) := by
    rw [ge_iff_le, le_div_iff₀ hk_pos, hR_def]
    have : d / (2 * k) * (2 * k) = d := div_mul_cancel₀ d (ne_of_gt hk2_pos)
    nlinarith
  have h2R1_pos : 2 * (R - 1) > 0 := by linarith
  have h1R_pos : 1 + R > 0 := by linarith
  have hpow : (2 * (R - 1)) ^ 4 ≥ 1 + R := power_ineq_for_chernoff R hR
  have hlog4 : 4 * Real.log (2 * (R - 1)) ≥ Real.log (1 + R) := by
    have : Real.log ((2 * (R - 1)) ^ 4) ≥ Real.log (1 + R) :=
      Real.log_le_log h1R_pos hpow
    rwa [Real.log_pow] at this
  calc k / 2 * Real.log ((d - 2 * k + 1) / k)
    ≥ k / 2 * Real.log (2 * (R - 1)) := by
      apply mul_le_mul_of_nonneg_left (Real.log_le_log h2R1_pos h_ratio_lb)
      linarith
    _ = k / 8 * (4 * Real.log (2 * (R - 1))) := by ring
    _ ≥ k / 8 * Real.log (1 + R) := by
      apply mul_le_mul_of_nonneg_left hlog4; linarith
    _ = k / 8 * Real.log (1 + d / (2 * k)) := by rw [hR_def]

end ChernoffHelpers

namespace ChernoffHelpers

/--
[exp_le_ratio_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma exp_le_ratio_pow
  {d k : ℝ}
-- given
  (hk : k ≥ 1)
  (hd : d ≥ 8 * k) :
-- imply
  Real.exp (k / 8 * Real.log (1 + d / (2 * k))) ≤ ((d - 2 * k + 1) / k) ^ (k / 2) := by
-- proof
  have h_base_pos : (d - 2 * k + 1) / k > 0 := by apply div_pos <;> linarith
  rw [rpow_def_of_pos h_base_pos]
  apply Real.exp_le_exp.mpr
  rw [mul_comm (Real.log _) _]
  exact log_ratio_bound d k hk hd

end ChernoffHelpers

namespace ChernoffHelpers

/--
[base_ratio_ge_six](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/ChernoffAnalyticHelpers.lean)
-/
@[path]
lemma base_ratio_ge_six
  {d k : ℕ}
-- given
  (_hk : 1 ≤ k)
  (hd : 8 * k ≤ d) :
-- imply
  6 * k ≤ d - 2 * k + 1 := by
-- proof
omega

end ChernoffHelpers


-- created on 2026-10-23
