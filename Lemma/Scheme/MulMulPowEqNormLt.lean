import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


private lemma l1_norm_coeff_le
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F : PowerSeries L)
  {ρ M : ℝ}
  (n : ℕ)
  -- given
  (hρ : 0 < ρ)
  (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) :
  -- imply
  ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n :=
  (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)

private lemma l1_norm_term_le
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F : PowerSeries L)
  {ρ M : ℝ}
  (a : L)
  (j m : ℕ)
  -- given
  (hρ : 0 < ρ)
  (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
  (ha : ‖a‖ < ρ) :
  -- imply
  ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := by
  -- proof
  rw [norm_mul, norm_pow, div_pow]
  have h1 := l1_norm_coeff_le F (j + m) hρ hF
  rw [pow_add] at h1
  have hρj : 0 < ρ ^ j := pow_pos hρ j
  have hρm : 0 < ρ ^ m := pow_pos hρ m
  calc
    _ ≤ M / (ρ ^ j * ρ ^ m) * ‖a‖ ^ m := by
      gcongr
    _ = M / ρ ^ j * (‖a‖ ^ m / ρ ^ m) := by
      field_simp

/--
[PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_tsum_coeff_mul_mul_pow_eq_of_norm_lt.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F G : PowerSeries L)
  {ρ M M' : ℝ}
  (z : L)
  -- given
  (hρ : 0 < ρ)
  (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
  (hG : ∀ n, ‖PowerSeries.coeff n G‖ * ρ ^ n ≤ M')
  (hz : ‖z‖ < ρ) :
  -- imply
  tsum (fun n => PowerSeries.coeff n (F * G) * z ^ n) = tsum (fun n => PowerSeries.coeff n F * z ^ n) * tsum (fun n => PowerSeries.coeff n G * z ^ n) := by
  -- proof
  have hr : ‖z‖ / ρ < 1 := (div_lt_one hρ).mpr hz
  have hr0 : 0 ≤ ‖z‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  have hFn : Summable (fun n => ‖PowerSeries.coeff n F * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ 0))
    simpa using l1_norm_term_le F z 0 n hρ hF hz
  have hGn : Summable (fun n => ‖PowerSeries.coeff n G * z ^ n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr).mul_left (M' / ρ ^ 0))
    simpa using l1_norm_term_le G z 0 n hρ hG hz
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hFn hGn]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring


-- created on 2026-10-20
