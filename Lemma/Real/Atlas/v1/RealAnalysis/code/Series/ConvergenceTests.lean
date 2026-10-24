import Mathlib
import sympy.Basic
open Filter Topology Real_Analysis


namespace Real_Analysis.Series

/--
[comparison_test](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean)
-/
@[path]
lemma comparison_test
  {x y : ℕ → ℝ}
-- given
  (hx : ∀ n, 0 ≤ x n)
  (hxy : ∀ n, x n ≤ y n) :
-- imply
  (Summable y → Summable x) ∧ (¬ Summable x → ¬ Summable y) := by
-- proof
  have h1 : Summable y → Summable x :=
    fun hy => Summable.of_nonneg_of_le hx hxy hy
  exact ⟨h1, fun hns hy => hns (h1 hy)⟩

end Real_Analysis.Series

namespace Real_Analysis.Series

/--
[root_test](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean)
-/
@[path]
lemma root_test
  {x : ℕ → ℝ}
  {L : ℝ}
-- given
  (hL : Tendsto (fun n => |x n| ^ ((1 : ℝ) / n)) atTop (nhds L)) :
-- imply
  (L < 1 → Summable (fun n => |x n|)) ∧ (1 < L → ¬ Summable x) := by
-- proof
  constructor
  ·
    intro hL1
    obtain ⟨r, hLr, hr1⟩ := exists_between hL1
    have hr0 : 0 ≤ r := by
      have : 0 ≤ L := by
        apply ge_of_tendsto hL
        apply eventually_atTop.mpr
        exact ⟨1, fun n _ => Real.rpow_nonneg (abs_nonneg _) _⟩
      linarith
    have hev : ∀ᶠ n in atTop, |x n| ^ ((1 : ℝ) / ↑n) < r := hL (Iio_mem_nhds hLr)
    apply Summable.of_norm_bounded_eventually_nat (g := fun n => r ^ n)
      (summable_geometric_of_lt_one hr0 hr1)
    have hev1 : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
    apply (hev.and hev1).mono
    intro n ⟨hn_lt, hn_pos⟩
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have hn_ne : (n : ℕ) ≠ 0 := by omega
    have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
    rw [h_eq] at hn_lt
    have h1 : (|x n| ^ ((↑n : ℝ)⁻¹)) ^ n ≤ r ^ n := by
      apply pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) _)
      exact le_of_lt hn_lt
    rwa [Real.rpow_inv_natCast_pow (abs_nonneg _) hn_ne] at h1
  ·
    intro hL1
    have hev : ∀ᶠ n in atTop, 1 < |x n| ^ ((1 : ℝ) / ↑n) := hL (Ioi_mem_nhds hL1)
    have hev1 : ∀ᶠ n in atTop, 1 < |x n| := by
      have hev_pos : ∀ᶠ n in atTop, (1 : ℕ) ≤ n := eventually_atTop.mpr ⟨1, fun n hn => hn⟩
      apply (hev.and hev_pos).mono
      intro n ⟨hn_gt, hn_pos⟩
      have hn_ne : (n : ℕ) ≠ 0 := by omega
      have h_eq : (1 : ℝ) / (↑n : ℝ) = (↑n : ℝ)⁻¹ := one_div _
      rw [h_eq] at hn_gt
      have h1 : (1 : ℝ) ^ n < (|x n| ^ ((↑n : ℝ)⁻¹)) ^ n := by
        apply pow_lt_pow_left₀ hn_gt (le_of_lt zero_lt_one) hn_ne
      rwa [one_pow, Real.rpow_inv_natCast_pow (abs_nonneg _) hn_ne] at h1
    intro hsum
    have h0 := hsum.tendsto_atTop_zero
    have h_abs0 : Tendsto (fun n => |x n|) atTop (nhds 0) := by
      rw [← abs_zero]; exact Tendsto.abs h0
    have h2 : ∀ᶠ n in atTop, |x n| < 1 := h_abs0 (Iio_mem_nhds one_pos)
    have h3 := h2.and hev1
    obtain ⟨n, hn1, hn2⟩ := h3.exists
    linarith

end Real_Analysis.Series

namespace Real_Analysis.Series

/--
[ratio_test](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean)
-/
@[path]
lemma ratio_test
  {x : ℕ → ℝ}
  {L : ℝ}
-- given
  (hx : ∀ n, x n ≠ 0)
  (hL : Filter.Tendsto (fun n => |x (n+1)| / |x n|) Filter.atTop (nhds L)) :
-- imply
  (L < 1 → Summable (fun n => |x n|)) ∧ (1 < L → ¬ Summable x) := by
-- proof
  constructor
  · intro hL1
    have hne : ∀ᶠ n in atTop, (fun n => |x n|) n ≠ 0 :=
      Filter.Eventually.of_forall (fun n => by simp [hx n])
    have htend : Tendsto (fun n => ‖(fun m => |x m|) (n + 1)‖ / ‖(fun m => |x m|) n‖) atTop (𝓝 L) := by
      simp only [Real.norm_eq_abs, abs_abs]
      exact hL
    exact summable_of_ratio_test_tendsto_lt_one hL1 hne htend
  · intro hL1
    have htend : Tendsto (fun n => ‖x (n + 1)‖ / ‖x n‖) atTop (𝓝 L) := by
      simp only [Real.norm_eq_abs]
      exact hL
    exact not_summable_of_ratio_test_tendsto_gt_one hL1 htend

end Real_Analysis.Series

namespace Real_Analysis.Series

/--
[alternating_series_test](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean)
-/
@[path]
lemma alternating_series_test
  {x : ℕ → ℝ}
-- given
  (hpos : ∀ n, 0 ≤ x n)
  (hdec : Antitone x)
  (hlim : Filter.Tendsto x Filter.atTop (nhds 0)) :
-- imply
  ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * x i) Filter.atTop (nhds l) := by
-- proof
  have _ := hpos
  exact hdec.tendsto_alternating_series_of_tendsto_zero hlim

end Real_Analysis.Series

namespace Real_Analysis.Series

/--
[alternating_harmonic_converges](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Series/ConvergenceTests.lean)
-/
@[path]
lemma alternating_harmonic_converges
-- imply
  ∃ l, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i / (↑i + 1))) Filter.atTop (nhds l) := by
-- proof
  have heq : (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i / (↑i + 1))) =
    (fun n => ∑ i ∈ Finset.range n, ((-1 : ℝ) ^ i * (1 / (↑i + 1)))) := by
    ext n; congr 1; ext i; ring
  rw [heq]
  have hdec : Antitone (fun n : ℕ => (1 : ℝ) / (↑n + 1)) := by
    intro a b hab
    apply div_le_div_of_nonneg_left
    · exact zero_lt_one.le
    · positivity
    · linarith [show (↑a : ℝ) ≤ ↑b from Nat.cast_le.mpr hab]
  have hlim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (nhds 0) := by
    have : Filter.Tendsto (fun n : ℕ => (↑n + 1 : ℝ)⁻¹) Filter.atTop (nhds 0) := by
      apply tendsto_inv_atTop_zero.comp
      exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simp only [div_eq_mul_inv, one_mul] at this ⊢
    exact this
  exact hdec.tendsto_alternating_series_of_tendsto_zero hlim

end Real_Analysis.Series


-- created on 2026-10-23
