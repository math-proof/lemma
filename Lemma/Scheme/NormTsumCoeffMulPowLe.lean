import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma l1_norm_coeff_le [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (n : ℕ) : ‖PowerSeries.coeff n F‖ ≤ M / ρ ^ n := (le_div_iff₀ (pow_pos hρ n)).mpr (hF n)
private lemma l1_M_nonneg [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) : 0 ≤ M := by
  have := hF 0
  simp only [pow_zero, mul_one] at this
  apply (norm_nonneg _).trans this
private lemma l1_norm_term_le [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (_ : ‖a‖ < ρ) (j m : ℕ) : ‖PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := by
  rw [norm_mul, norm_pow, div_pow]
  have h1 := l1_norm_coeff_le F hρ hF (j + m)
  rw [pow_add] at h1
  have hρj : 0 < ρ ^ j := pow_pos hρ j
  have hρm : 0 < ρ ^ m := pow_pos hρ m
  calc
    _ ≤ M / (ρ ^ j * ρ ^ m) * ‖a‖ ^ m := by gcongr
    _ = M / ρ ^ j * (‖a‖ ^ m / ρ ^ m) := by field_simp
private lemma l1_summable_shifted [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) : Summable (fun m : ℕ => PowerSeries.coeff (j + m) F * a ^ m) := by
  have hr : ‖a‖ / ρ < 1 := (div_lt_one hρ).mpr ha
  have hr0 : 0 ≤ ‖a‖ / ρ := div_nonneg (norm_nonneg _) hρ.le
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr).mul_left (M / ρ ^ j)) (fun m => l1_norm_term_le F hρ hF a ha j m)
private lemma l1_norm_tsum_shifted_le [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L] (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M) (a : L) (ha : ‖a‖ < ρ) (j : ℕ) : ‖∑' m : ℕ, PowerSeries.coeff (j + m) F * a ^ m‖ ≤ M / ρ ^ j := by
  have hM := l1_M_nonneg F hF
  have hC : 0 ≤ M / ρ ^ j := div_nonneg hM (pow_pos hρ j).le
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hC fun m => ?_
  have hr1 : (‖a‖ / ρ) ^ m ≤ 1 := pow_le_one₀ (div_nonneg (norm_nonneg _) hρ.le) ((div_le_one hρ).mpr ha.le)
  calc
    _ ≤ M / ρ ^ j * (‖a‖ / ρ) ^ m := l1_norm_term_le F hρ hF a ha j m
    _ ≤ M / ρ ^ j * 1 := by gcongr
    _ = M / ρ ^ j := mul_one _
/--
[PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_summable_and_norm_tsum_coeff_mul_pow_le.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (F : PowerSeries L) {ρ M : ℝ} (hρ : 0 < ρ) (hF : ∀ n, ‖PowerSeries.coeff n F‖ * ρ ^ n ≤ M)
  (z : L) (hz : ‖z‖ < ρ) :
  -- imply
  Summable (fun n => PowerSeries.coeff n F * z ^ n) ∧ ‖∑' n, PowerSeries.coeff n F * z ^ n‖ ≤ M := by
  -- proof
  have h1 := l1_summable_shifted F hρ hF z hz 0
  have h2 := l1_norm_tsum_shifted_le F hρ hF z hz 0
  simp only [zero_add, pow_zero, div_one] at h1 h2
  exact ⟨h1, h2⟩


-- created on 2026-10-20
