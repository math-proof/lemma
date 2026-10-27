/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Def.Analysis.SpecialFunctions.CatalanConstantProducts.Part7


section

namespace MetaMathlibExt

theorem ccp_atan_term_nonneg (t : ℝ) (n : ℕ) (ht : 0 ≤ t) :
    0 ≤ ccp_atan_term t n := by
  unfold ccp_atan_term
  positivity

theorem ccp_atan_term_antitone (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Antitone (ccp_atan_term t) := by
  intro k l hkl
  have hexp : 2 * k ≤ 2 * l := by omega
  have hpow : t ^ (2 * l) ≤ t ^ (2 * k) :=
    pow_le_pow_of_le_one ht0 ht1 hexp
  have hden : (2 : ℝ) * (k : ℝ) + 1 ≤ 2 * (l : ℝ) + 1 := by
    exact_mod_cast (show 2 * k + 1 ≤ 2 * l + 1 by omega)
  unfold ccp_atan_term
  calc
    t ^ (2 * l) / (2 * (l : ℝ) + 1) ≤
        t ^ (2 * l) / (2 * (k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (pow_nonneg ht0 _) (by positivity) hden
    _ ≤ t ^ (2 * k) / (2 * (k : ℝ) + 1) :=
      div_le_div_of_nonneg_right hpow (by positivity)

theorem ccp_atan_partial_norm_le_one (N : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖ccp_atan_partial N t‖ ≤ 1 := by
  have hbounds := ccp_alt_sum_bounds (ccp_atan_term t)
    (fun n => ccp_atan_term_nonneg t n ht0) (ccp_atan_term_antitone t ht0 ht1) N
  rw [ccp_atan_partial, Real.norm_eq_abs, abs_of_nonneg hbounds.1]
  simpa [ccp_atan_term] using hbounds.2

theorem ccp_atan_partial_tendsto (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    Filter.Tendsto (fun N : ℕ => ccp_atan_partial N t) Filter.atTop
      (nhds (Real.arctan t / t)) := by
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  have hsum := (Real.hasSum_arctan hnorm).div_const t
  have hterm : (fun n : ℕ =>
      ((-1 : ℝ) ^ n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) / t) =
      (fun n : ℕ => (-1 : ℝ) ^ n * ccp_atan_term t n) := by
    funext n
    unfold ccp_atan_term
    rw [pow_succ]
    field_simp
    push_cast
    rfl
  rw [hterm] at hsum
  simpa [ccp_atan_partial, ccp_alt_sum] using hsum.tendsto_sum_nat

theorem ccp_atan_integral_tendsto :
    Filter.Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..1, ccp_atan_partial N t)
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, Real.arctan t / t)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  · refine Filter.Eventually.of_forall fun N => ?_
    have hmeas : Measurable (fun t : ℝ => ccp_atan_partial N t) := by
      unfold ccp_atan_partial ccp_alt_sum ccp_atan_term
      fun_prop
    exact hmeas.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun N => ?_
    filter_upwards [] with t
    intro ht
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at ht
    exact ccp_atan_partial_norm_le_one N t ht.1.le ht.2
  · exact intervalIntegrable_const
  · filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (1 : ℝ)] with t ht1
    intro ht
    rw [Set.uIoc_of_le (by norm_num), Set.mem_Ioc] at ht
    exact ccp_atan_partial_tendsto t ht.1 (lt_of_le_of_ne ht.2 ht1)

theorem ccp_atan_term_integral (n : ℕ) :
    (∫ t in (0 : ℝ)..1, (-1 : ℝ) ^ n * ccp_atan_term t n) =
      (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold ccp_atan_term
  have heq : (fun t : ℝ => (-1 : ℝ) ^ n * (t ^ (2 * n) / (2 * (n : ℝ) + 1))) =
      (fun t : ℝ => ((-1 : ℝ) ^ n * t ^ (2 * n)) / (2 * (n : ℝ) + 1)) := by
    funext t
    ring
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_pow]
  norm_num
  field_simp

theorem ccp_atan_partial_integral (N : ℕ) :
    (∫ t in (0 : ℝ)..1, ccp_atan_partial N t) =
      ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2 := by
  unfold ccp_atan_partial ccp_alt_sum
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact ccp_atan_term_integral n
  · intro n hn
    have hcont : Continuous (fun t : ℝ => (-1 : ℝ) ^ n * ccp_atan_term t n) := by
      unfold ccp_atan_term
      fun_prop
    exact hcont.intervalIntegrable 0 1

theorem ccp_atan_integral_eq (G : ℝ)
    (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (∫ t in (0 : ℝ)..1, Real.arctan t / t) = G := by
  have hint : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N,
        (-1 : ℝ) ^ n / (2 * (n : ℝ) + 1) ^ 2)
      Filter.atTop (nhds (∫ t in (0 : ℝ)..1, Real.arctan t / t)) := by
    simpa only [ccp_atan_partial_integral] using ccp_atan_integral_tendsto
  exact tendsto_nhds_unique hint hG.tendsto_sum_nat

theorem ccp_sinc_pos (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) :
    0 < Real.sinc x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hxpi : x < Real.pi := by linarith [Real.pi_pos]
    rw [Real.sinc_of_ne_zero hx]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hxpos hxpi) hxpos

theorem ccp_continuousOn_inv_sinc :
    ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹) (Set.Icc 0 (Real.pi / 2)) := by
  apply Real.continuous_sinc.continuousOn.inv₀
  intro x hx
  exact (ccp_sinc_pos x hx.1 hx.2).ne'

theorem ccp_catFlim_eq_inv_sinc (u : ℝ) :
    catFlim u = (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹ - 1 / 2 := by
  by_cases hu : u = 0
  · subst u
    simp [catFlim]
  · have hx : Real.pi * u / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero Real.pi_ne_zero hu) (by norm_num)
    unfold catFlim
    simp only [hu, ite_false]
    rw [Real.sinc_of_ne_zero hx, inv_div]
    ring

theorem ccp_inv_sinc_integral_scale :
    (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) =
      (2 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Real.pi * v / 2) (Real.pi / 2) u := by
    intro u hu
    simpa only [div_eq_mul_inv, id_eq, one_mul, mul_assoc, mul_comm] using
      (hasDerivAt_id u).const_mul (Real.pi / 2)
  have hcont : ContinuousOn (fun _ : ℝ => Real.pi / 2) (Set.uIcc (0 : ℝ) 1) :=
    continuousOn_const
  have hg : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      ((fun u : ℝ => Real.pi * u / 2) '' Set.uIcc (0 : ℝ) 1) := by
    apply ccp_continuousOn_inv_sinc.mono
    rintro x ⟨u, hu, rfl⟩
    rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at hu
    constructor <;> nlinarith [Real.pi_pos]
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun u : ℝ => Real.pi * u / 2)
    (f' := fun _ : ℝ => Real.pi / 2) (g := fun x : ℝ => (Real.sinc x)⁻¹)
    hderiv hcont hg
  have hsubst' :
      (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹ * (Real.pi / 2)) =
        ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
    simpa [Function.comp_apply] using hsubst
  rw [intervalIntegral.integral_mul_const] at hsubst'
  calc
    (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) =
        (2 / Real.pi) *
          ((∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) *
            (Real.pi / 2)) := by
      field_simp
    _ = (2 / Real.pi) * ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
      rw [hsubst']

theorem ccp_inv_sinc_arctan_mul (t : ℝ) (ht : t ≠ 0) :
    (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2)) =
      2 * (Real.arctan t / t) := by
  have hatan : Real.arctan t ≠ 0 := Real.arctan_eq_zero_iff.not.mpr ht
  have htwoatan : 2 * Real.arctan t ≠ 0 := mul_ne_zero (by norm_num) hatan
  have hsqrt : Real.sqrt (1 + t ^ 2) ≠ 0 := by positivity
  have hsquare : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
    Real.sq_sqrt (by positivity)
  rw [Real.sinc_of_ne_zero htwoatan, inv_div, Real.sin_two_mul,
    Real.sin_arctan, Real.cos_arctan]
  field_simp
  nlinarith

theorem ccp_inv_sinc_integral_arctan :
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹) =
      2 * ∫ t in (0 : ℝ)..1, Real.arctan t / t := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => 2 * Real.arctan s) (2 / (1 + t ^ 2)) t := by
    intro t ht
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using
      (Real.hasDerivAt_arctan t).const_mul 2
  have hcont : ContinuousOn (fun t : ℝ => 2 / (1 + t ^ 2))
      (Set.uIcc (0 : ℝ) 1) := by
    apply Continuous.continuousOn
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      positivity
  have hg : ContinuousOn (fun x : ℝ => (Real.sinc x)⁻¹)
      ((fun t : ℝ => 2 * Real.arctan t) '' Set.uIcc (0 : ℝ) 1) := by
    apply ccp_continuousOn_inv_sinc.mono
    rintro x ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le (by norm_num), Set.mem_Icc] at ht
    have hatan0 : 0 ≤ Real.arctan t := Real.arctan_nonneg.mpr ht.1
    have hatan1 : Real.arctan t ≤ Real.pi / 4 := by
      rw [← Real.arctan_one]
      exact Real.arctan_le_arctan_iff.mpr ht.2
    constructor <;> linarith
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := 1) (f := fun t : ℝ => 2 * Real.arctan t)
    (f' := fun t : ℝ => 2 / (1 + t ^ 2)) (g := fun x : ℝ => (Real.sinc x)⁻¹)
    hderiv hcont hg
  have hsubst' :
      (∫ t in (0 : ℝ)..1,
        (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2))) =
        ∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹ := by
    rw [Real.arctan_one] at hsubst
    have hend : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    rw [hend] at hsubst
    simpa [Function.comp_apply] using hsubst
  have hcongr :
      (∫ t in (0 : ℝ)..1,
        (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2))) =
        ∫ t in (0 : ℝ)..1, 2 * (Real.arctan t / t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (0 : ℝ)] with t ht
    intro hmem
    exact ccp_inv_sinc_arctan_mul t ht
  calc
    (∫ x in (0 : ℝ)..Real.pi / 2, (Real.sinc x)⁻¹) =
        ∫ t in (0 : ℝ)..1,
          (Real.sinc (2 * Real.arctan t))⁻¹ * (2 / (1 + t ^ 2)) := hsubst'.symm
    _ = ∫ t in (0 : ℝ)..1, 2 * (Real.arctan t / t) := hcongr
    _ = 2 * ∫ t in (0 : ℝ)..1, Real.arctan t / t := by
      rw [intervalIntegral.integral_const_mul]

theorem ccp_catFlim_integral_eq_inv_sinc :
    (∫ u in (0 : ℝ)..1, catFlim u) =
      (1 / 2) * (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) - 1 / 2 := by
  have hcont : ContinuousOn (fun u : ℝ => (Real.sinc (Real.pi * u / 2))⁻¹)
      (Set.Icc (0 : ℝ) 1) := by
    have hsinc : Continuous (fun u : ℝ => Real.sinc (Real.pi * u / 2)) := by
      fun_prop
    apply hsinc.continuousOn.inv₀
    intro u hu
    apply (ccp_sinc_pos (Real.pi * u / 2) ?_ ?_).ne'
    · have hpi : 0 < Real.pi := Real.pi_pos
      exact div_nonneg (mul_nonneg hpi.le hu.1) (by norm_num)
    · have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [hu.2]
  have hint : IntervalIntegrable (fun u : ℝ => (Real.sinc (Real.pi * u / 2))⁻¹)
      MeasureTheory.volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num)
  calc
    (∫ u in (0 : ℝ)..1, catFlim u) =
        ∫ u in (0 : ℝ)..1, (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹ - 1 / 2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact ccp_catFlim_eq_inv_sinc u
    _ = (∫ u in (0 : ℝ)..1, (1 / 2) * (Real.sinc (Real.pi * u / 2))⁻¹) -
        ∫ _ in (0 : ℝ)..1, (1 / 2 : ℝ) := by
      rw [intervalIntegral.integral_sub (hint.const_mul (1 / 2)) intervalIntegrable_const]
    _ = (1 / 2) * (∫ u in (0 : ℝ)..1, (Real.sinc (Real.pi * u / 2))⁻¹) -
        1 / 2 := by
      rw [intervalIntegral.integral_const_mul]
      norm_num

theorem ccp_catFlim_integral_eq (G : ℝ)
    (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (∫ u in (0 : ℝ)..1, catFlim u) = 2 * G / Real.pi - 1 / 2 := by
  rw [ccp_catFlim_integral_eq_inv_sinc, ccp_inv_sinc_integral_scale,
    ccp_inv_sinc_integral_arctan, ccp_atan_integral_eq G hG]
  field_simp

/--
Three infinite product formulas for exponentials of Catalan's constant
`G`: `exp (2 * G / π - 1 / 2)` and `exp (2 * G / π + 1 / 2)` as limits of
`∏_{n=1}^{2m}` and `∏_{n=1}^{2m+1}` of `(1 - 2 / (2n+1)) ^ (n * (-1)^n)`,
and `exp (4 * G / π)` as the limit of the squared quotient of
`(4k+3)^(4k+3)` over `(4k+1)^(4k+1)` products with the boundary factor
`(4m+3)^(2m+1) / (4m+1)^(6m+1)`, with `G` specified by its alternating
reciprocal-squares series.

Source: Yasuyuki Kachi and Pavlos Tzermias, "Infinite Products Involving
ζ(3) and Catalan's Constant," Journal of Integer Sequences 15 (2012),
Article 12.9.4, Proposition (label catalan), equations (labels catalani,
catalanii, catalaniii), lines 147–165,
https://cs.uwaterloo.ca/journals/JIS/VOL15/Tzermias/tzermias2.tex

The products over `Finset.range m` of `(4k+3)^(4k+3)` and `(4k+1)^(4k+1)`
are the source's `3^3 · 7^7 ⋯ (4m-1)^(4m-1)` and
`1^1 · 5^5 ⋯ (4m-3)^(4m-3)`. All three limits were confirmed numerically
(first two to ~1e-12 at `m = 200000`, the third to ~5e-7 via a
cancellation-free reformulation).

Proves `Wanted` entry `catalan_constant_product_formulas`.

Proof: Following Kachi and Tzermias, Proposition (catalan), dominated convergence reduces the
product limit to the cosecant integral. The substitutions `x = πu/2` and `x = 2 arctan t`, followed
by the arctangent power series, evaluate it in terms of `G`.
-/
theorem catalan_constant_product_formulas
    (G : ℝ) (hG : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((2 * (n : ℝ) + 1) ^ 2)) G) :
    (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m),
        (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi - 1 / 2)))) ∧
    (Filter.Tendsto (fun m : ℕ => ∏ n ∈ Finset.Icc 1 (2 * m + 1),
        (1 - 2 / (2 * (n : ℝ) + 1)) ^ ((n : ℤ) * (-1 : ℤ) ^ n))
      Filter.atTop (nhds (Real.exp (2 * G / Real.pi + 1 / 2)))) ∧
    Filter.Tendsto (fun m : ℕ =>
        ((∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) /
          (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1))) ^ 2 *
        (4 * (m : ℝ) + 3) ^ (2 * m + 1) / (4 * (m : ℝ) + 1) ^ (6 * m + 1))
      Filter.atTop (nhds (Real.exp (4 * G / Real.pi))) := by
  have hlog : Filter.Tendsto (fun m : ℕ => Real.log (catP m))
      Filter.atTop (nhds (2 * G / Real.pi - 1 / 2)) := by
    have hint := ccp_catFint_integral_tendsto
    rw [ccp_catFlim_integral_eq G hG] at hint
    refine Filter.Tendsto.congr (fun m => ?_) hint
    exact (catP_log_eq_integral m).symm
  have hP : Filter.Tendsto catP Filter.atTop
      (nhds (Real.exp (2 * G / Real.pi - 1 / 2))) := catP_of_log G hlog
  refine ⟨?_, ?_, ?_⟩
  · exact hP
  · exact catQ_of_catP G hP
  · exact catR_of_catPQ G hP (catQ_of_catP G hP)

end MetaMathlibExt
end
