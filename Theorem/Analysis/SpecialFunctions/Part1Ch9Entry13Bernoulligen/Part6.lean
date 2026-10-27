/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.SpecialFunctions.Part1Ch9Entry13Bernoulligen.Part6
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch9

namespace Entry13Bernoulligen

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Filter Finset Topology MeasureTheory

noncomputable section

theorem entry13_G_hasDerivAt (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    HasDerivAt (fun y => entry13G n r y) (x ^ n * entry13K r x) x := by
  have hterm : ∀ j ∈ Finset.range (n + 1), HasDerivAt
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
          + x ^ (n - j) * entry13Cp j r x)) x :=
    fun j _ => entry13_Gterm_hasDerivAt n j hr0 hr1 x
  have hsum := HasDerivAt.sum hterm
  have hneg := hsum.neg
  have hfun : (-(∑ j ∈ Finset.range (n + 1),
      (fun y => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
        * y ^ (n - j) * entry13C (j + 1) r y)))
      = (fun y => entry13G n r y) := by
    funext y
    unfold entry13G
    simp only [Pi.neg_apply, Finset.sum_apply]
  rw [hfun] at hneg
  have hPn : entry13s n * (n.factorial : ℝ) / ((n - n).factorial : ℝ)
        * (((n - n : ℕ) : ℝ) * x ^ (n - n - 1) * entry13C (n + 1) r x)
      = 0 := by
    have h0 : ((n - n : ℕ) : ℝ) = 0 := by simp
    simp only [h0, zero_mul, mul_zero]
  have hQ0 : entry13s 0 * (n.factorial : ℝ) / ((n - 0).factorial : ℝ)
        * (x ^ (n - 0) * entry13Cp 0 r x)
      = -(x ^ n * entry13K r x) := by
    have hs0 : entry13s 0 = 1 := by
      unfold entry13s
      simp
    have hCp0 : entry13Cp 0 r x = -entry13K r x := by
      unfold entry13Cp
      simp only [ite_true]
    have hfn0 : (n.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    rw [hs0, hCp0, Nat.sub_zero, one_mul, div_self hfn0, one_mul]
    ring
  have hpair : ∀ j ∈ Finset.range n,
      (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x)
        + entry13s (j + 1) * (n.factorial : ℝ) / ((n - (j + 1)).factorial : ℝ)
          * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    exact entry13_cancel_pair n j hjn x
  have hderiv : -(∑ j ∈ Finset.range (n + 1),
        entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x
            + x ^ (n - j) * entry13Cp j r x))
      = x ^ n * entry13K r x := by
    simp only [left_distrib]
    rw [Finset.sum_add_distrib]
    have hP : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x))
          = ∑ j ∈ Finset.range n,
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x) := by
      rw [Finset.sum_range_succ _ n, hPn, add_zero]
    have hQ : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * (x ^ (n - j) * entry13Cp j r x))
          = (∑ j ∈ Finset.range n,
              entry13s (j + 1) * (n.factorial : ℝ)
                / ((n - (j + 1)).factorial : ℝ)
                * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x))
            + entry13s 0 * (n.factorial : ℝ) / ((n - 0).factorial : ℝ)
              * (x ^ (n - 0) * entry13Cp 0 r x) :=
      Finset.sum_range_succ' _ n
    rw [hP, hQ, hQ0]
    have hpair0 : (∑ j ∈ Finset.range n,
              entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
                * (((n - j : ℕ) : ℝ) * x ^ (n - j - 1) * entry13C (j + 1) r x))
            + (∑ j ∈ Finset.range n,
              entry13s (j + 1) * (n.factorial : ℝ)
                / ((n - (j + 1)).factorial : ℝ)
                * (x ^ (n - (j + 1)) * entry13Cp (j + 1) r x)) = 0 := by
      rw [← Finset.sum_add_distrib]
      trans ∑ _j ∈ Finset.range n, (0 : ℝ)
      · exact Finset.sum_congr rfl hpair
      · exact Finset.sum_const_zero
    linarith [hpair0]
  rw [hderiv] at hneg
  exact hneg

theorem entry13_G_zero (n : ℕ) (r : ℝ) :
    entry13G n r 0
      = -(entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0) := by
  have h0 : (∑ j ∈ Finset.range n,
        entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * (0 : ℝ) ^ (n - j) * entry13C (j + 1) r 0) = 0 := by
    trans ∑ _j ∈ Finset.range n, (0 : ℝ)
    · apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hne : n - j ≠ 0 := by omega
      have hpow : (0 : ℝ) ^ (n - j) = 0 := zero_pow hne
      simp only [hpow, mul_zero, zero_mul]
    · exact Finset.sum_const_zero
  unfold entry13G
  rw [Finset.sum_range_succ _ n, h0, zero_add]
  have hnn : n - n = 0 := Nat.sub_self n
  rw [hnn]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]

theorem entry13K_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u => entry13K r u) := by
  unfold entry13K entry13D
  apply Continuous.div
  · continuity
  · continuity
  · intro u
    exact entry13D_ne_zero hr0 hr1 u

theorem entry13_powK_intervalIntegrable (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (x : ℝ) :
    IntervalIntegrable (fun u => u ^ n * entry13K r u) MeasureTheory.volume 0 x :=
  ((continuous_pow n).mul (entry13K_continuous hr0 hr1)).continuousOn.intervalIntegrable

theorem entry13_H3_identity (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (x : ℝ) :
    (∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      = entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
        - ∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * entry13C (j + 1) r x := by
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt (fun y => entry13G n r y) (y ^ n * entry13K r y) y :=
    fun y _ => entry13_G_hasDerivAt n hr0 hr1 y
  have hint := entry13_powK_intervalIntegrable n hr0 hr1 x
  have hFTC : (∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      = entry13G n r x - entry13G n r 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [entry13_G_zero] at hFTC
  unfold entry13G at hFTC
  linear_combination hFTC

/-! ## Step 4a: the left-side limit by dominated convergence -/

theorem entry13_eventually_mem_Ioo :
    ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), r ∈ Set.Ioo (0 : ℝ) 1 := by
  have h1 : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), r < 1 :=
    self_mem_nhdsWithin
  have h0 : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), 0 < r :=
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [h0, h1] with r hr0 hr1
  exact ⟨hr0, hr1⟩

theorem entry13_abs_le_of_mem_uIcc {x u : ℝ} (hu : u ∈ Set.uIcc 0 x) :
    |u| ≤ |x| := by
  rw [Set.mem_uIcc] at hu
  rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · by_cases hxnn : 0 ≤ x
    · calc |u| = u := abs_of_nonneg (by linarith)
        _ ≤ x := h2
        _ = |x| := (abs_of_nonneg hxnn).symm
    · have hxlt : x < 0 := lt_of_not_ge hxnn
      linarith
  · by_cases hxnn : x ≤ 0
    · calc |u| = -u := abs_of_nonpos (by linarith)
        _ ≤ -x := by linarith
        _ = |x| := (abs_of_nonpos hxnn).symm
    · have hxlt : 0 < x := lt_of_not_ge hxnn
      linarith

theorem entry13_tendsto_D (u : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13D r u) (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (2 - 2 * Real.cos u)) := by
  have hcont : Continuous (fun r : ℝ => entry13D r u) := by
    unfold entry13D
    continuity
  have h1 : entry13D 1 u = 2 - 2 * Real.cos u := by
    unfold entry13D
    ring
  have h : Filter.Tendsto (fun r : ℝ => entry13D r u)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (entry13D 1 u)) :=
    (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
  rwa [h1] at h

theorem entry13_two_sub_cos_pos {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    0 < 2 - 2 * Real.cos u := by
  have habs : |u| < 2 * Real.pi :=
    lt_of_le_of_lt (entry13_abs_le_of_mem_uIcc hu) hx
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hiff := Real.cos_eq_one_iff_of_lt_of_lt hlo hhi
  have hne : Real.cos u ≠ 1 := by
    intro hcon
    rw [hiff] at hcon
    exact hu0 hcon
  have hle : Real.cos u ≤ 1 := Real.cos_le_one u
  have hlt : Real.cos u < 1 := lt_of_le_of_ne hle hne
  linarith

theorem entry13_tendsto_K {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIcc 0 x) (hu0 : u ≠ 0) :
    Filter.Tendsto (fun r : ℝ => entry13K r u) (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (Real.sin u / (2 - 2 * Real.cos u))) := by
  have hD := entry13_tendsto_D u
  have hpos := entry13_two_sub_cos_pos hx hu hu0
  have hne : (2 : ℝ) - 2 * Real.cos u ≠ 0 := ne_of_gt hpos
  have hnum : Filter.Tendsto (fun r : ℝ => r * Real.sin u)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (1 * Real.sin u)) := by
    have hc : Continuous (fun _ : ℝ => Real.sin u) := continuous_const
    exact ((continuous_id.mul hc).tendsto 1).mono_left nhdsWithin_le_nhds
  have hdiv : Filter.Tendsto (fun r : ℝ => r * Real.sin u / entry13D r u)
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (1 * Real.sin u / (2 - 2 * Real.cos u))) :=
    hnum.div hD hne
  have hfun : (fun r : ℝ => r * Real.sin u / entry13D r u)
      = (fun r => entry13K r u) := by
    funext r
    unfold entry13K
    rfl
  have hval : (1 : ℝ) * Real.sin u / (2 - 2 * Real.cos u)
      = Real.sin u / (2 - 2 * Real.cos u) := by
    rw [one_mul]
  rw [hfun, hval] at hdiv
  exact hdiv

theorem entry13_dominated (n : ℕ) {r u : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    ‖u ^ n * entry13K r u‖ ≤ ‖chapter9Entry13Integrand n u‖ := by
  have hr0 : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  have hDpos : 0 < entry13D r u := entry13D_pos hr0.le hr1 u
  have hDge : 4 * r * Real.sin (u / 2) ^ 2 ≤ entry13D r u := by
    have h1 := entry13D_ge_two_mul r u
    rw [entry13_one_sub_cos] at h1
    have heq : 2 * r * (2 * Real.sin (u / 2) ^ 2)
        = 4 * r * Real.sin (u / 2) ^ 2 := by ring
    rwa [heq] at h1
  by_cases hs : Real.sin (u / 2) = 0
  · have hsin : Real.sin u = 0 := by
      conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
      rw [hs]
      ring
    have hK : entry13K r u = 0 := by
      unfold entry13K
      rw [hsin, mul_zero, zero_div]
    rw [hK, mul_zero, norm_zero]
    exact norm_nonneg _
  · have habs_pos : (0 : ℝ) < |Real.sin (u / 2)| := abs_pos.mpr hs
    have hsq_pos : (0 : ℝ) < Real.sin (u / 2) ^ 2 := by
      have h1 : (0 : ℝ) < |Real.sin (u / 2)| ^ 2 := pow_pos habs_pos 2
      rwa [sq_abs] at h1
    have h4pos : (0 : ℝ) < 4 * r * Real.sin (u / 2) ^ 2 := by positivity
    have hle : (r * |Real.sin u|) / entry13D r u
        ≤ (r * |Real.sin u|) / (4 * r * Real.sin (u / 2) ^ 2) := by
      have hnn : (0 : ℝ) ≤ r * |Real.sin u| := by positivity
      have hdiv : 1 / entry13D r u ≤ 1 / (4 * r * Real.sin (u / 2) ^ 2) :=
        one_div_le_one_div_of_le h4pos hDge
      calc (r * |Real.sin u|) / entry13D r u
          = (r * |Real.sin u|) * (1 / entry13D r u) := by
            rw [div_eq_mul_one_div]
        _ ≤ (r * |Real.sin u|) * (1 / (4 * r * Real.sin (u / 2) ^ 2)) :=
            mul_le_mul_of_nonneg_left hdiv hnn
        _ = (r * |Real.sin u|) / (4 * r * Real.sin (u / 2) ^ 2) :=
            (div_eq_mul_one_div _ _).symm
    have hcancel : r * |Real.sin u| / (4 * r * Real.sin (u / 2) ^ 2)
        = |Real.sin u| / (4 * Real.sin (u / 2) ^ 2) := by
      have h1 : (4 : ℝ) * r * Real.sin (u / 2) ^ 2 ≠ 0 := ne_of_gt h4pos
      have h2 : (4 : ℝ) * Real.sin (u / 2) ^ 2 ≠ 0 :=
        ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    have hsin2 : |Real.sin u|
        = 2 * |Real.sin (u / 2)| * |Real.cos (u / 2)| := by
      have habs2 : |(2 : ℝ)| = 2 := by norm_num
      conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
      rw [abs_mul, abs_mul, habs2]
    have hfinal : |Real.sin u| / (4 * Real.sin (u / 2) ^ 2)
        = |Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|) := by
      rw [hsin2, ← sq_abs (Real.sin (u / 2))]
      have hsq2 : (0 : ℝ) < |Real.sin (u / 2)| ^ 2 := pow_pos habs_pos 2
      have h1 : (4 : ℝ) * |Real.sin (u / 2)| ^ 2 ≠ 0 := ne_of_gt (by positivity)
      have h2 : (2 : ℝ) * |Real.sin (u / 2)| ≠ 0 := ne_of_gt (by positivity)
      rw [div_eq_div_iff h1 h2]
      ring
    have e2 : (r * |Real.sin u| / entry13D r u)
        ≤ |Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|) := by
      rw [hcancel] at hle
      exact hle.trans_eq hfinal
    have e1 : |u ^ n * entry13K r u|
        = |u| ^ n * (r * |Real.sin u| / entry13D r u) := by
      unfold entry13K
      rw [abs_mul, abs_pow, abs_div, abs_mul, abs_of_pos hr0, abs_of_pos hDpos]
    have e3 : |chapter9Entry13Integrand n u|
        = |u| ^ n * (|Real.cos (u / 2)| / (2 * |Real.sin (u / 2)|)) := by
      unfold chapter9Entry13Integrand
      have habs2 : |(2 : ℝ)| = 2 := by norm_num
      rw [abs_mul, abs_div, abs_div, abs_pow, habs2]
      ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e1, e3]
    exact mul_le_mul_of_nonneg_left e2 (pow_nonneg (abs_nonneg u) n)

theorem entry13_K_limit_value (n : ℕ) {x u : ℝ} (hx : |x| < 2 * Real.pi)
    (hu : u ∈ Set.uIoc 0 x) (hu0 : u ≠ 0) :
    u ^ n * (Real.sin u / (2 - 2 * Real.cos u))
      = chapter9Entry13Integrand n u := by
  have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
  have hs0 : Real.sin (u / 2) ≠ 0 := sin_half_ne_zero_of_mem hx huIcc hu0
  have hsin : Real.sin u = 2 * Real.sin (u / 2) * Real.cos (u / 2) := by
    conv_lhs => rw [show u = 2 * (u / 2) from by ring, Real.sin_two_mul]
  have hcos : 2 - 2 * Real.cos u = 4 * Real.sin (u / 2) ^ 2 := by
    have h := entry13_one_sub_cos u
    linarith
  have hs2 : Real.sin (u / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have h1 : (4 : ℝ) * Real.sin (u / 2) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) hs2
  have h2 : (2 : ℝ) * Real.sin (u / 2) ≠ 0 :=
    mul_ne_zero two_ne_zero hs0
  unfold chapter9Entry13Integrand
  rw [hsin, hcos, ← mul_div_assoc, div_mul_div_comm, div_eq_div_iff h1 h2]
  ring

theorem entry13_tendsto_integral (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto (fun r : ℝ => ∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖chapter9Entry13Integrand n u‖)
  · filter_upwards [entry13_eventually_mem_Ioo] with r hr
    have hcont : Continuous (fun u => u ^ n * entry13K r u) :=
      (continuous_pow n).mul (entry13K_continuous hr.1.le hr.2)
    exact hcont.continuousOn.aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [entry13_eventually_mem_Ioo] with r hr
    filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with u _hu0
    intro _
    exact entry13_dominated n hr
  · exact (entry13_intervalIntegrable n x hn hx).norm
  · filter_upwards [MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with u hu0
    intro hu
    have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
    have hK := entry13_tendsto_K hx huIcc hu0
    have hlim : Filter.Tendsto (fun r : ℝ => u ^ n * entry13K r u)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (u ^ n * (Real.sin u / (2 - 2 * Real.cos u)))) :=
      tendsto_const_nhds.mul hK
    rwa [entry13_K_limit_value n hx hu hu0] at hlim

/-! ## Step 4b: limits of the regularized Clausen sums -/

theorem entry13_cm_tendsto (m : ℕ) (hm : 2 ≤ m) (x : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13cm m r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen m x)) := by
  have hf : ∀ k : ℕ, ContinuousOn
      (fun r : ℝ => r ^ (k + 1) * chapter9ClausenTerm m x k) (Set.Icc 0 1) :=
    fun k => ((continuous_pow (k + 1)).mul continuous_const).continuousOn
  have hu : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) :=
    chapter9ClausenTerm_shift_summable m hm
  have hfu : ∀ k (r : ℝ), r ∈ Set.Icc 0 1 →
      ‖r ^ (k + 1) * chapter9ClausenTerm m x k‖
        ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) := by
    intro k r hr
    have hr0 : 0 ≤ r := hr.1
    have hr1 : r ≤ 1 := hr.2
    have hpow : ‖r ^ (k + 1)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr0 _)]
      exact pow_le_one₀ hr0 hr1
    have hT := chapter9ClausenTerm_norm_bound m x k
    have hnn : (0 : ℝ) ≤ ‖chapter9ClausenTerm m x k‖ := norm_nonneg _
    calc ‖r ^ (k + 1) * chapter9ClausenTerm m x k‖
        = ‖r ^ (k + 1)‖ * ‖chapter9ClausenTerm m x k‖ := norm_mul _ _
      _ ≤ 1 * ‖chapter9ClausenTerm m x k‖ :=
          mul_le_mul_of_nonneg_right hpow hnn
      _ ≤ 1 * ((1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m)) :=
          mul_le_mul_of_nonneg_left hT (by norm_num)
      _ = (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ m) := one_mul _
  have h := continuousOn_tsum hf hu hfu
  have hfun : (fun r => ∑' k : ℕ, r ^ (k + 1) * chapter9ClausenTerm m x k)
      = (fun r => entry13cm m r x) := rfl
  rw [hfun] at h
  have hmem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
    Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
  have htend : Filter.Tendsto (fun r : ℝ => entry13cm m r x)
      (nhdsWithin 1 (Set.Icc 0 1)) (𝓝 (entry13cm m 1 x)) :=
    h.continuousWithinAt hmem
  have hval : entry13cm m 1 x = chapter9Clausen m x := by
    unfold entry13cm chapter9Clausen
    have hm0 : ¬m = 0 := by omega
    have hm1 : ¬m = 1 := by omega
    simp only [hm0, hm1, ite_false]
    apply tsum_congr
    intro k
    rw [one_pow, one_mul]
  rw [hval] at htend
  have hIoo_le : nhdsWithin (1 : ℝ) (Set.Ioo 0 1)
      ≤ nhdsWithin (1 : ℝ) (Set.Icc 0 1) :=
    nhdsWithin_mono 1 Set.Ioo_subset_Icc_self
  have htend2 := htend.mono_left hIoo_le
  have hfilter : nhdsWithin (1 : ℝ) (Set.Iio 1)
      = nhdsWithin (1 : ℝ) (Set.Ioo 0 1) := by
    have hmemIoi : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) :=
      Set.mem_Ioi.mpr (show (0 : ℝ) < 1 by norm_num)
    have hinter : Set.Iio (1 : ℝ) ∩ Set.Ioi 0 = Set.Ioo 0 1 ∩ Set.Ioi 0 := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, Set.mem_Ioo]
      tauto
    exact nhdsWithin_eq_nhdsWithin hmemIoi isOpen_Ioi hinter
  rwa [← hfilter] at htend2

theorem entry13_C_tendsto (j : ℕ) (hj : 1 ≤ j) (x : ℝ) :
    Filter.Tendsto (fun r : ℝ => entry13C (j + 1) r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (j + 1) x)) := by
  have hfun : (fun r : ℝ => entry13C (j + 1) r x)
      = (fun r : ℝ => entry13cm (j + 1) r x) := by
    funext r
    unfold entry13C
    have h : j + 1 ≠ 1 := by omega
    simp only [h, ite_false]
  rw [hfun]
  have hm : 2 ≤ j + 1 := by omega
  exact entry13_cm_tendsto (j + 1) hm x

/-! ## Step 4c: limit of the closed-form logarithm -/

theorem entry13_c1closed_tendsto (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen 1 x)) := by
  have hxmem : x ∈ Set.uIcc 0 x := Set.right_mem_uIcc
  have hD := entry13_tendsto_D x
  have hpos : 0 < 2 - 2 * Real.cos x :=
    entry13_two_sub_cos_pos hx hxmem hx0
  have hlog : Filter.Tendsto (fun r : ℝ => Real.log (entry13D r x))
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 (Real.log (2 - 2 * Real.cos x))) :=
    (Real.continuousAt_log (ne_of_gt hpos)).tendsto.comp hD
  have hmul : Filter.Tendsto (fun r : ℝ => -(1 / 2) * Real.log (entry13D r x))
      (nhdsWithin 1 (Set.Iio 1))
      (𝓝 (-(1 / 2) * Real.log (2 - 2 * Real.cos x))) :=
    tendsto_const_nhds.mul hlog
  have hfun : (fun r : ℝ => -(1 / 2) * Real.log (entry13D r x))
      = (fun r => entry13c1closed r x) := by
    funext r
    unfold entry13c1closed
    rfl
  rw [hfun] at hmul
  have hsq : 2 - 2 * Real.cos x = (2 * Real.sin (x / 2)) ^ 2 := by
    have h := entry13_one_sub_cos x
    have h2 : (2 * Real.sin (x / 2)) ^ 2 = 4 * Real.sin (x / 2) ^ 2 := by ring
    linarith
  have hval : -(1 / 2 : ℝ) * Real.log (2 - 2 * Real.cos x)
      = chapter9Clausen 1 x := by
    unfold chapter9Clausen
    have h10 : ¬(1 : ℕ) = 0 := one_ne_zero
    simp only [h10, ite_false, ite_true]
    rw [hsq, Real.log_pow]
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2, Real.log_abs]
    ring
  rw [hval] at hmul
  exact hmul

/-! ## Step 4d: the constant term -/

theorem entry13_clausen_zero_of_odd (n : ℕ) (hn : 1 ≤ n) (hodd : Odd n) :
    chapter9Clausen (n + 1) 0 = 0 := by
  have hne0 : n + 1 ≠ 0 := by omega
  have hne1 : n + 1 ≠ 1 := by omega
  have hev : Even (n + 1) := hodd.add_one
  unfold chapter9Clausen
  simp only [hne0, hne1, ite_false]
  have hT : ∀ k : ℕ, chapter9ClausenTerm (n + 1) 0 k = 0 := by
    intro k
    unfold chapter9ClausenTerm
    simp only [hev, ite_true, mul_zero, Real.sin_zero, zero_div]
  trans ∑' _k : ℕ, (0 : ℝ)
  · exact tsum_congr hT
  · exact tsum_zero

theorem entry13_cos_odd (n : ℕ) (hodd : Odd n) :
    Real.cos ((n : ℝ) * Real.pi / 2) = 0 := by
  obtain ⟨m, hm⟩ := hodd
  have hmR : (n : ℝ) = 2 * (m : ℝ) + 1 := by exact_mod_cast hm
  have harg : (n : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi + Real.pi / 2 := by
    rw [hmR]
    ring
  rw [harg, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  ring

theorem entry13_clausen_zero_of_even (n m : ℕ) (hn : 1 ≤ n)
    (hn2 : n = 2 * m) :
    chapter9Clausen (n + 1) 0
      = ∑' k : ℕ, (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ) ^ (n + 1) := by
  have hne0 : n + 1 ≠ 0 := by omega
  have hne1 : n + 1 ≠ 1 := by omega
  have hodd : Odd (n + 1) := ⟨m, by rw [hn2]⟩
  have hneven : ¬Even (n + 1) := Nat.not_even_iff_odd.mpr hodd
  unfold chapter9Clausen
  simp only [hne0, hne1, ite_false]
  apply tsum_congr
  intro k
  unfold chapter9ClausenTerm
  simp only [hneven, ite_false, mul_zero, Real.cos_zero]

theorem entry13s_even (n m : ℕ) (hn2 : n = 2 * m) :
    entry13s n = (-1 : ℝ) ^ m := by
  have hexp : n * (n + 1) / 2 = m * (2 * m + 1) := by
    have hmul : n * (n + 1) = 2 * (m * (2 * m + 1)) := by
      rw [hn2]
      ring
    rw [hmul]
    exact Nat.mul_div_cancel_left (m * (2 * m + 1)) (by norm_num : (0 : ℕ) < 2)
  have hpow : (-1 : ℝ) ^ (m * (2 * m + 1)) = (-1 : ℝ) ^ m := by
    have heq : m * (2 * m + 1) = m + 2 * (m * m) := by ring
    rw [heq, pow_add]
    have h1 : (-1 : ℝ) ^ (2 * (m * m)) = 1 := by
      rw [pow_mul, neg_one_sq, one_pow]
    rw [h1, mul_one]
  unfold entry13s
  rw [hexp]
  exact hpow

theorem entry13_cos_even (n m : ℕ) (hn2 : n = 2 * m) :
    Real.cos ((n : ℝ) * Real.pi / 2) = (-1 : ℝ) ^ m := by
  have hnR : (n : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hn2
  have harg : (n : ℝ) * Real.pi / 2 = (m : ℝ) * Real.pi := by
    rw [hnR]
    ring
  rw [harg, Real.cos_nat_mul_pi]

theorem entry13_zeta_re (n : ℕ) (hn : 1 ≤ n) :
    (∑' k : ℕ, (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ (n + 1)))
      = (riemannZeta (((n + 1 : ℕ)) : ℂ)).re := by
  have hs : (1 : ℝ) < ((((n + 1 : ℕ)) : ℂ)).re := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_re]
    have h : (1 : ℕ) < n + 1 := by omega
    exact_mod_cast h
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow
    (s := (((n + 1 : ℕ)) : ℂ)) hs
  have hsumC : Summable
      (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ)) := by
    have hbase : Summable
        (fun k : ℕ => (1 : ℂ) / (k : ℂ) ^ (((n + 1 : ℕ)) : ℂ)) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have hshift := (summable_nat_add_iff 1).mpr hbase
    have hfun : (fun k : ℕ => (1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ))
        = (fun k : ℕ => (1 : ℂ) / (((k + 1 : ℕ)) : ℂ) ^ (((n + 1 : ℕ)) : ℂ)) := by
      funext k
      simp only [Nat.cast_add_one]
    rw [hfun]
    exact hshift
  have hre := Complex.re_tsum hsumC
  rw [← hz] at hre
  have hterm : ∀ k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) ^ (((n + 1 : ℕ)) : ℂ)).re
      = (1 : ℝ) / (((k + 1 : ℕ)) : ℝ) ^ (n + 1) := by
    intro k
    rw [← Nat.cast_add_one, Complex.cpow_natCast, ← Nat.cast_pow,
      ← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_div,
      Complex.ofReal_re, Nat.cast_pow]
  rw [tsum_congr hterm] at hre
  exact hre.symm

theorem entry13_const_term (n : ℕ) (hn : 1 ≤ n) :
    entry13s n * chapter9Clausen (n + 1) 0
      = Real.cos ((n : ℝ) * Real.pi / 2)
        * (riemannZeta ((((n + 1 : ℕ))) : ℂ)).re := by
  rcases Nat.even_or_odd n with hev | hodd
  · obtain ⟨m, hm⟩ := hev
    have hn2 : n = 2 * m := by omega
    have hCl := entry13_clausen_zero_of_even n m hn hn2
    have hzeta := entry13_zeta_re n hn
    have hs := entry13s_even n m hn2
    have hc := entry13_cos_even n m hn2
    rw [hCl, hzeta, hs, hc]
  · have hCl0 := entry13_clausen_zero_of_odd n hn hodd
    have hc0 := entry13_cos_odd n hodd
    rw [hCl0, hc0, mul_zero, zero_mul]

/-! ## Conjunct 2: Dirichlet plus Abel -/

theorem entry13_exp_pow (x : ℝ) (m : ℕ) :
    Complex.exp ((x : ℂ) * Complex.I) ^ m
      = Complex.exp (((((m : ℝ) * x : ℝ)) : ℂ) * Complex.I) := by
  have harg : (m : ℂ) * ((x : ℂ) * Complex.I)
      = (((((m : ℝ) * x : ℝ))) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul, Complex.ofReal_natCast]
    ring
  rw [← Complex.exp_nat_mul, harg]

theorem entry13_exp_pow_re (x : ℝ) (m : ℕ) :
    (Complex.exp ((x : ℂ) * Complex.I) ^ m).re
      = Real.cos ((m : ℝ) * x) := by
  rw [entry13_exp_pow, Complex.exp_ofReal_mul_I_re]

theorem entry13_geom_bound (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    ∃ b : ℝ, ∀ n : ℕ, ‖∑ i ∈ Finset.range n,
      Real.cos (((((i + 1 : ℕ))) : ℝ) * x)‖ ≤ b := by
  have hw1 : Complex.exp ((x : ℂ) * Complex.I) ≠ 1 := by
    intro hcon
    have hre : (Complex.exp ((x : ℂ) * Complex.I)).re = (1 : ℂ).re := by
      rw [hcon]
    rw [Complex.exp_ofReal_mul_I_re, Complex.one_re] at hre
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    have hiff := Real.cos_eq_one_iff_of_lt_of_lt hlo hhi
    rw [hiff] at hre
    exact hx0 hre
  have hw10 : (1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := by
    intro hcon
    apply hw1
    have h := sub_eq_zero.mp hcon
    exact h.symm
  have hc : (0 : ℝ) < ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr hw10
  have hw1norm : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I x
  refine ⟨2 / ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖, fun n => ?_⟩
  have hRe : (∑ i ∈ Finset.range n, Real.cos (((((i + 1 : ℕ))) : ℝ) * x))
      = (∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [entry13_exp_pow_re]
  have hsum : (∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1))
      = Complex.exp ((x : ℂ) * Complex.I)
        * ((Complex.exp ((x : ℂ) * Complex.I) ^ n - 1)
          / (Complex.exp ((x : ℂ) * Complex.I) - 1)) := by
    have h1 : (∑ i ∈ Finset.range n,
          Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1))
        = (∑ i ∈ Finset.range n, Complex.exp ((x : ℂ) * Complex.I) ^ i)
          * Complex.exp ((x : ℂ) * Complex.I) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact pow_succ _ _
    rw [h1, geom_sum_eq hw1]
    ring
  have hwn : ‖Complex.exp ((x : ℂ) * Complex.I) ^ n‖ = 1 := by
    rw [norm_pow, hw1norm, one_pow]
  have h2 : ‖Complex.exp ((x : ℂ) * Complex.I) ^ n - 1‖ ≤ 2 := by
    have h := norm_sub_le (Complex.exp ((x : ℂ) * Complex.I) ^ n) 1
    rw [hwn, norm_one] at h
    have h11 : (1 : ℝ) + 1 = 2 := by norm_num
    rwa [h11] at h
  have hboundC : ‖∑ i ∈ Finset.range n,
        Complex.exp ((x : ℂ) * Complex.I) ^ (i + 1)‖
      ≤ 2 / ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ := by
    rw [hsum, norm_mul, hw1norm, one_mul, norm_div]
    have hrev : ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖
        = ‖(1 : ℂ) - Complex.exp ((x : ℂ) * Complex.I)‖ :=
      norm_sub_rev _ _
    rw [hrev, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hc.le)
  rw [Real.norm_eq_abs, hRe]
  exact le_trans (Complex.abs_re_le_norm _) hboundC

theorem entry13_dirichlet_limit (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    ∃ l : ℝ, Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 l) := by
  have hanti : Antitone (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ)) := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · have h0 : (0 : ℕ) < a + 1 := by omega
      exact_mod_cast h0
    · exact_mod_cast Nat.add_le_add_right hab 1
  have hzero : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
      atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ))) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto
        (fun k : ℕ => (fun n : ℕ => (1 : ℝ) / ((n : ℝ))) (k + 1))
        atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).mpr h
    exact h2
  obtain ⟨b, hb⟩ := entry13_geom_bound x hx0 hx
  have hdir := Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    (f := fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
    (z := fun k : ℕ => Real.cos (((k + 1 : ℕ) : ℝ) * x))
    hanti hzero hb
  obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hdir
  refine ⟨l, ?_⟩
  have hsmul : ∀ k : ℕ, ((1 : ℝ) / ((((k + 1 : ℕ))) : ℝ))
        • Real.cos (((k + 1 : ℕ) : ℝ) * x)
      = Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro k
    rw [smul_eq_mul]
    ring
  have h2 := hl
  simp only [hsmul] at h2
  exact h2

theorem entry13_conjunct2 (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < 2 * Real.pi) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 (chapter9Clausen 1 x)) := by
  obtain ⟨l, hl⟩ := entry13_dirichlet_limit x hx0 hx
  have hTS : ∀ n : ℕ, (∑ i ∈ Finset.range (n + 1),
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      = ∑ k ∈ Finset.range n,
        Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ) := by
    intro n
    rw [Finset.sum_range_succ']
    have hf0 : Real.cos (((0 : ℕ) : ℝ) * x) / ((0 : ℕ) : ℝ) = 0 := by simp
    rw [hf0, add_zero]
  have hTshift : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      atTop (𝓝 l) := by
    have hfun : (fun n : ℕ => ∑ i ∈ Finset.range (n + 1),
          Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
        = (fun N : ℕ => ∑ k ∈ Finset.range N,
          Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ)) :=
      funext hTS
    rw [hfun]
    exact hl
  have hT : Filter.Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range n,
        Real.cos (((i : ℕ) : ℝ) * x) / ((i : ℕ) : ℝ))
      atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).mp hTshift
  have habel := Real.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n : ℕ => Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) hT
  have hid : ∀ r : ℝ, 0 ≤ r → r < 1 →
      (∑' n : ℕ, (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n)
        = entry13c1closed r x := by
    intro r hr0 hr1
    have hH1 := (entry13_H1_unshifted hr0 hr1 x).tsum_eq
    have hterm : ∀ n : ℕ, (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n
        = r ^ n * Real.cos ((n : ℝ) * x) / (n : ℝ) := by
      intro n
      ring
    rw [tsum_congr hterm]
    exact hH1
  have hc1l : Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
      (nhdsWithin 1 (Set.Iio 1)) (𝓝 l) := by
    have heq : (fun r : ℝ => ∑' n : ℕ,
            (Real.cos (((n : ℕ) : ℝ) * x) / ((n : ℕ) : ℝ)) * r ^ n)
          =ᶠ[nhdsWithin 1 (Set.Iio 1)] (fun r : ℝ => entry13c1closed r x) := by
      filter_upwards [entry13_eventually_mem_Ioo] with r hr
      exact hid r hr.1.le hr.2
    exact Filter.Tendsto.congr' heq habel
  have hc1Cl := entry13_c1closed_tendsto x hx0 hx
  have hl_eq : l = chapter9Clausen 1 x := tendsto_nhds_unique hc1l hc1Cl
  rw [hl_eq] at hl
  exact hl

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.

Proves `Wanted` entry `ramanujan_part1_ch9_entry13_bernoulligen`.
-/
theorem ramanujan_part1_ch9_entry13_bernoulligen (n : ℕ) (x : ℝ)
    (hn : 1 ≤ n) (hx0 : x ≠ 0) (hx : |x| < 2 * Real.pi) :
    IntervalIntegrable (chapter9Entry13Integrand n) volume 0 x ∧
      Tendsto
        (fun N : ℕ => ∑ k ∈ range N,
          Real.cos (((k + 1 : ℕ) : ℝ) * x) / ((k + 1 : ℕ) : ℝ))
        atTop (𝓝 (chapter9Clausen 1 x)) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ n + 1 →
        Summable (chapter9ClausenTerm m x)) ∧
      (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u) =
        Real.cos (n * Real.pi / 2) * n.factorial *
            (riemannZeta ((n + 1 : ℕ) : ℂ)).re -
          ∑ j ∈ range (n + 1),
            (-1 : ℝ) ^ (j * (j + 1) / 2) *
              (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9Clausen (j + 1) x := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact entry13_intervalIntegrable n x hn hx
  · exact entry13_conjunct2 x hx0 hx
  · intro m hm2 _hmn
    exact chapter9ClausenTerm_summable_of_two_le m x hm2
  · have hL := entry13_tendsto_integral n x hn hx
    have hC0 : Filter.Tendsto (fun r : ℝ => entry13C (n + 1) r 0)
        (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (n + 1) 0)) :=
      entry13_C_tendsto n hn 0
    have hconst : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0)) :=
      tendsto_const_nhds.mul hC0
    have hterm : ∀ j ∈ Finset.range (n + 1), Filter.Tendsto
        (fun r : ℝ => entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
          * x ^ (n - j) * chapter9Clausen (j + 1) x)) := by
      intro j hj
      by_cases hj0 : j = 0
      · subst hj0
        have hC1 : Filter.Tendsto (fun r : ℝ => entry13C (0 + 1) r x)
            (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen (0 + 1) x)) := by
          have hfun : (fun r : ℝ => entry13C (0 + 1) r x)
              = (fun r : ℝ => entry13c1closed r x) := by
            funext r
            unfold entry13C
            simp
          have hCl : Filter.Tendsto (fun r : ℝ => entry13c1closed r x)
              (nhdsWithin 1 (Set.Iio 1)) (𝓝 (chapter9Clausen 1 x)) :=
            entry13_c1closed_tendsto x hx0 hx
          rw [hfun]
          simpa using hCl
        exact tendsto_const_nhds.mul hC1
      · have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
        have hC := entry13_C_tendsto j hj1 x
        exact tendsto_const_nhds.mul hC
    have hsum : Filter.Tendsto
        (fun r : ℝ => ∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (∑ j ∈ Finset.range (n + 1),
          entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
            * x ^ (n - j) * chapter9Clausen (j + 1) x)) :=
      tendsto_finsetSum _ hterm
    have hR : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x)) :=
      hconst.sub hsum
    have heq : (fun r : ℝ => ∫ u in (0 : ℝ)..x, u ^ n * entry13K r u)
        =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x) := by
      filter_upwards [entry13_eventually_mem_Ioo] with r hr
      exact entry13_H3_identity n hr.1.le hr.2 x
    have hR' : Filter.Tendsto
        (fun r : ℝ => entry13s n * (n.factorial : ℝ) * entry13C (n + 1) r 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * entry13C (j + 1) r x)
        (nhdsWithin 1 (Set.Iio 1))
        (𝓝 (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)) :=
      Filter.Tendsto.congr' heq hL
    have hEq : (∫ u in (0 : ℝ)..x, chapter9Entry13Integrand n u)
        = entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
          - ∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x :=
      tendsto_nhds_unique hR' hR
    have hct := entry13_const_term n hn
    have hconstEq : entry13s n * (n.factorial : ℝ) * chapter9Clausen (n + 1) 0
        = Real.cos (n * Real.pi / 2) * n.factorial *
          (riemannZeta ((n + 1 : ℕ) : ℂ)).re := by
      have hfac : ((n.factorial : ℕ) : ℝ) = (n.factorial : ℝ) := rfl
      linear_combination (n.factorial : ℝ) * hct
    have hsumEq : (∑ j ∈ Finset.range (n + 1),
            entry13s j * (n.factorial : ℝ) / ((n - j).factorial : ℝ)
              * x ^ (n - j) * chapter9Clausen (j + 1) x)
        = ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (j * (j + 1) / 2) *
              (n.factorial : ℝ) / ((n - j).factorial : ℝ) *
              x ^ (n - j) * chapter9Clausen (j + 1) x := by
      apply Finset.sum_congr rfl
      intro j _
      rfl
    rw [hEq, hconstEq, hsumEq]

end
end Entry13Bernoulligen
end Ramanujan.Part1Ch9
end
