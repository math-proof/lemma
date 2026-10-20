/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Log/IntegralDerivative.lean -/

import sympy.atlas.Analysis.SpecialFunctions.Log.Integral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic integral — real-valued chart for the derivative

The source definition `Real.logarithmicIntegral` is on the subtype
`Real.LogarithmicIntegralDomain = {x : ℝ // 0 ≤ x ∧ x ≠ 1}`
(papers 2306.14073v1:284-287, 2309.16007v1:112-115,
`li(x) = ∫₀ˣ dt / log t`, Cauchy principal value; `x = 1` excluded as the
singularity `1/log t` at `t=1` is non-integrable). Lean's `HasDerivAt` expects
`ℝ → ℝ`.

## Representation choice

We provide a single global extension `Real.logarithmicIntegralReal : ℝ → ℝ`
that agrees with `Real.logarithmicIntegral` on `0 ≤ x ∧ x ≠ 1` and is `0`
(junk) elsewhere. This is the smallest reusable chart:

* it does not redefine or renormalize the integral — the paired symmetric
  principal value `∫₀¹ ((log(1-u))⁻¹ + (log(1+u))⁻¹)` for `x > 1` and the
  ordinary `∫₀ˣ` for `0 ≤ x < 1` are preserved verbatim via
  `logarithmicIntegral`;
* at any `x₀ > 0, x₀ ≠ 1` there is a neighbourhood `I` (`(0,1)` if `x₀ < 1`,
  `(1,∞)` if `x₀ > 1`) contained in the domain on which the extension
  coincides with the integral, so `HasDerivAt` at `x₀` is independent of the
  junk value outside `I`;
* a per-point local chart `fun x in I ↦ li x` would be equivalent but forces
  a subtype coercion in every derivative statement; the global extension lets
  the derivative be stated as `HasDerivAt Real.logarithmicIntegralReal
  (1 / Real.log x) x` with hypotheses `0 < x` and `x ≠ 1`.

The derivative `1 / Real.log x` is the local FTC consequence
`d/dx ∫ dt/log t = 1/log x` via continuity of `t ↦ (log t)⁻¹` at `t = x ≠ 1`.
The theorem below supplies the full local FTC proof on both sides of the singularity.
-/

open scoped Topology

namespace Real

/-- Global real-valued extension of `logarithmicIntegral`.

Agrees with `Real.logarithmicIntegral` on `0 ≤ x ∧ x ≠ 1` and is `0`
elsewhere (junk). At `x > 0, x ≠ 1` the value is locally determined by the
integral, so `HasDerivAt` at such `x` does not depend on the junk choice. -/
noncomputable def logarithmicIntegralReal (x : ℝ) : ℝ :=
  if h : 0 ≤ x ∧ x ≠ 1 then
    Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain)
  else
    0

@[simp]
theorem logarithmicIntegralReal_zero : Real.logarithmicIntegralReal 0 = 0 := by
  have h : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≠ 1 := ⟨by norm_num, by norm_num⟩
  simp [Real.logarithmicIntegralReal, h, Real.logarithmicIntegral_zero]

theorem logarithmicIntegralReal_of_mem {x : ℝ} (h : 0 ≤ x ∧ x ≠ 1) :
    Real.logarithmicIntegralReal x =
      Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain) := by
  simp [Real.logarithmicIntegralReal, h]

-- Branch lemmas avoid rewriting `logarithmicIntegralReal_of_mem` to preserve
-- the named opaque def `Real.LogarithmicIntegralDomain`. The pair
-- `⟨x, h⟩ : Real.LogarithmicIntegralDomain` must not be inferred as the raw
-- subtype `{x // 0 ≤ x ∧ x ≠ 1}`; we prove agreement by unfolding
-- `logarithmicIntegralReal` with `dite_eq_left` and then applying the existing
-- `logarithmicIntegral_of_*` lemmas with an explicitly typed `val` hypothesis.

theorem logarithmicIntegralReal_of_lt_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.logarithmicIntegralReal x = ∫ t in (0 : ℝ)..x, (Real.log t)⁻¹ := by
  have h : 0 ≤ x ∧ x ≠ 1 := ⟨hx0, ne_of_lt hx1⟩
  have hx1' : ((⟨x, h⟩ : Real.LogarithmicIntegralDomain).val < 1) := hx1
  -- Expand the extension at the domain point without going through the raw-subtype rewrite.
  have h1 : Real.logarithmicIntegralReal x =
      Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain) := by
    simp only [Real.logarithmicIntegralReal, dite_eq_left h]
  rw [h1, Real.logarithmicIntegral_of_lt_one hx1']

theorem logarithmicIntegralReal_of_one_lt {x : ℝ} (hx : 1 < x) :
    Real.logarithmicIntegralReal x =
      (∫ u in (0 : ℝ)..(1 : ℝ), ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
        ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹ := by
  have h0 : 0 ≤ x := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) hx)
  have h : 0 ≤ x ∧ x ≠ 1 := ⟨h0, ne_of_gt hx⟩
  have hx' : (1 < (⟨x, h⟩ : Real.LogarithmicIntegralDomain).val) := hx
  have h1 : Real.logarithmicIntegralReal x =
      Real.logarithmicIntegral (⟨x, h⟩ : Real.LogarithmicIntegralDomain) := by
    simp only [Real.logarithmicIntegralReal, dite_eq_left h]
  rw [h1, Real.logarithmicIntegral_of_one_lt hx']

/-- Derivative of the real-valued logarithmic integral away from one.

For `0 < x`, `x ≠ 1`, `Real.logarithmicIntegralReal` has derivative
`1 / Real.log x` at `x`. This is the local FTC for `li(x) = ∫₀ˣ dt / log t`:
below `1` the chart agrees with `∫₀ˣ` near `x`, above `1` it agrees with a
paired principal-value constant plus `∫₂ˣ`, whose derivative is `(log x)⁻¹`.
-/
theorem hasDerivAt_logarithmicIntegralReal {x : ℝ}
    (hx_pos : 0 < x) (hx_ne_one : x ≠ 1) :
    HasDerivAt Real.logarithmicIntegralReal (1 / Real.log x) x := by
  have hcont_at : ∀ {y : ℝ}, 0 < y → y ≠ 1 →
      ContinuousAt (fun t => (Real.log t)⁻¹) y := by
    intro y hy0 hy1
    have hy_ne0 : y ≠ 0 := ne_of_gt hy0
    have hlog_ne : Real.log y ≠ 0 := by
      rcases lt_or_gt_of_ne hy1 with hlt | hgt
      · have hneg : Real.log y < 0 := Real.log_neg hy0 hlt
        exact ne_of_lt hneg
      · have hpos : 0 < Real.log y := Real.log_pos hgt
        exact ne_of_gt hpos
    exact (Real.continuousAt_log hy_ne0).inv₀ hlog_ne
  have hf_zero : (fun t : ℝ => (Real.log t)⁻¹) 0 = 0 := by
    simp
  have h_log_NE : Filter.Tendsto Real.log (𝓝[≠] (0 : ℝ)) Filter.atBot :=
    Real.tendsto_log_nhdsNE_zero
  have h_ne : Filter.Tendsto (fun t : ℝ => (Real.log t)⁻¹)
      (𝓝[({0} : Set ℝ)ᶜ] (0 : ℝ)) (𝓝 0) :=
    h_log_NE.inv_tendsto_atBot
  have h_single : Filter.Tendsto (fun t : ℝ => (Real.log t)⁻¹)
      (𝓝[({0} : Set ℝ)] (0 : ℝ)) (𝓝 0) := by
    have heq : (fun t : ℝ => (Real.log t)⁻¹) =ᶠ[𝓝[({0} : Set ℝ)] (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      apply Filter.eventuallyEq_of_mem self_mem_nhdsWithin
      intro t ht
      have ht0 : t = 0 := ht
      subst ht0
      exact hf_zero
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  have h_nhds_eq : 𝓝 (0 : ℝ) =
      𝓝[({0} : Set ℝ)ᶜ] (0 : ℝ) ⊔ 𝓝[({0} : Set ℝ)] (0 : ℝ) := by
    have h := nhdsWithin_union (0 : ℝ) (({0} : Set ℝ)ᶜ) ({0} : Set ℝ)
    have hunion : (({0} : Set ℝ)ᶜ ∪ {0}) = Set.univ := by
      ext t
      by_cases h : t = 0 <;> simp [h]
    rw [hunion, nhdsWithin_univ] at h
    exact h
  have h_tendsto : Filter.Tendsto (fun t : ℝ => (Real.log t)⁻¹)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    conv_lhs => rw [h_nhds_eq]
    exact h_ne.sup h_single
  have hcont_zero : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) 0 := by
    change Filter.Tendsto (fun t : ℝ => (Real.log t)⁻¹) (𝓝 (0 : ℝ))
      (𝓝 ((fun t : ℝ => (Real.log t)⁻¹) 0))
    rw [hf_zero]
    exact h_tendsto
  rcases lt_or_gt_of_ne hx_ne_one with hx_lt_one | hx_gt_one
  · have hmeas : StronglyMeasurableAtFilter
        (fun t : ℝ => (Real.log t)⁻¹) (𝓝 x) MeasureTheory.volume := by
      refine ContinuousAt.stronglyMeasurableAtFilter
        (f := fun t : ℝ => (Real.log t)⁻¹)
        (μ := MeasureTheory.volume)
        (s := Set.Ioo (0 : ℝ) 1) isOpen_Ioo ?_ x
        (Set.mem_Ioo.mpr ⟨hx_pos, hx_lt_one⟩)
      intro y hy
      have hym : 0 < y ∧ y < 1 := Set.mem_Ioo.mp hy
      exact hcont_at hym.1 (ne_of_lt hym.2)
    have hcont_Icc : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹)
        (Set.Icc 0 x) := by
      intro t ht
      have ht_mem : 0 ≤ t ∧ t ≤ x := Set.mem_Icc.mp ht
      rcases eq_or_lt_of_le ht_mem.1 with h0 | ht0pos
      · subst h0
        exact hcont_zero.continuousWithinAt
      · have ht_ne0 : t ≠ 0 := ne_of_gt ht0pos
        have ht_lt1 : t < 1 := lt_of_le_of_lt ht_mem.2 hx_lt_one
        have ht_ne1 : t ≠ 1 := ne_of_lt ht_lt1
        exact (hcont_at ht0pos ht_ne1).continuousWithinAt
    have hu : Set.uIcc (0 : ℝ) x = Set.Icc 0 x :=
      Set.uIcc_of_le (le_of_lt hx_pos)
    have hInt : IntervalIntegrable
        (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 0 x := by
      have h : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Set.uIcc 0 x) := by
        rw [hu]
        exact hcont_Icc
      exact h.intervalIntegrable
    have hFTC : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, (Real.log t)⁻¹)
        ((Real.log x)⁻¹) x :=
      intervalIntegral.integral_hasDerivAt_right hInt hmeas
        (hcont_at hx_pos hx_ne_one)
    have hmem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 x :=
      Ioo_mem_nhds hx_pos hx_lt_one
    have heq : Real.logarithmicIntegralReal =ᶠ[𝓝 x]
        (fun y => ∫ t in (0 : ℝ)..y, (Real.log t)⁻¹) := by
      apply Filter.eventuallyEq_of_mem hmem
      intro y hy
      have hym : 0 < y ∧ y < 1 := Set.mem_Ioo.mp hy
      have hy0 : 0 ≤ y := le_of_lt hym.1
      exact Real.logarithmicIntegralReal_of_lt_one hy0 hym.2
    have hD := hFTC.congr_of_eventuallyEq heq
    simpa [one_div] using hD
  · have hcont_uIcc : ContinuousOn (fun t : ℝ => (Real.log t)⁻¹)
        (Set.uIcc 2 x) := by
      intro t ht
      have ht1 : 1 < t := by
        rcases le_total 2 x with hle | hle
        · have hmem : t ∈ Set.Icc (2 : ℝ) x := by
            have hu : Set.uIcc (2 : ℝ) x = Set.Icc 2 x := Set.uIcc_of_le hle
            rwa [hu] at ht
          have h2t : (2 : ℝ) ≤ t := (Set.mem_Icc.mp hmem).1
          exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h2t
        · have hmem : t ∈ Set.Icc x (2 : ℝ) := by
            have hu : Set.uIcc (2 : ℝ) x = Set.Icc x 2 := Set.uIcc_of_ge hle
            rwa [hu] at ht
          have hxt : x ≤ t := (Set.mem_Icc.mp hmem).1
          exact lt_of_lt_of_le hx_gt_one hxt
      have ht_pos : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht1
      have ht_ne1 : t ≠ 1 := ne_of_gt ht1
      exact (hcont_at ht_pos ht_ne1).continuousWithinAt
    have hInt : IntervalIntegrable
        (fun t : ℝ => (Real.log t)⁻¹) MeasureTheory.volume 2 x :=
      hcont_uIcc.intervalIntegrable
    have hmeas : StronglyMeasurableAtFilter
        (fun t : ℝ => (Real.log t)⁻¹) (𝓝 x) MeasureTheory.volume := by
      refine ContinuousAt.stronglyMeasurableAtFilter
        (f := fun t : ℝ => (Real.log t)⁻¹)
        (μ := MeasureTheory.volume)
        (s := Set.Ioi (1 : ℝ)) isOpen_Ioi ?_ x
        (Set.mem_Ioi.mpr hx_gt_one)
      intro y hy
      have hy1 : 1 < y := Set.mem_Ioi.mp hy
      have hy0 : 0 < y := lt_trans (by norm_num : (0 : ℝ) < 1) hy1
      exact hcont_at hy0 (ne_of_gt hy1)
    have hFTC : HasDerivAt (fun y => ∫ t in (2 : ℝ)..y, (Real.log t)⁻¹)
        ((Real.log x)⁻¹) x :=
      intervalIntegral.integral_hasDerivAt_right hInt hmeas
        (hcont_at hx_pos hx_ne_one)
    have hC : HasDerivAt (fun y =>
          (∫ u in (0 : ℝ)..(1 : ℝ),
            ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
          ∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) ((Real.log x)⁻¹) x := by
      have hconst : HasDerivAt (fun _ : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ),
          ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) 0 x :=
        hasDerivAt_const x _
      have h := hconst.add hFTC
      have hfun : (fun y : ℝ =>
            (∫ u in (0 : ℝ)..(1 : ℝ),
              ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
            ∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) =
          ((fun _ : ℝ => ∫ u in (0 : ℝ)..(1 : ℝ),
              ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
            (fun y => ∫ t in (2 : ℝ)..y, (Real.log t)⁻¹)) :=
        funext fun y => rfl
      rw [hfun]
      simpa only [zero_add] using h
    have hmem : Set.Ioi (1 : ℝ) ∈ 𝓝 x := Ioi_mem_nhds hx_gt_one
    have heq : Real.logarithmicIntegralReal =ᶠ[𝓝 x] (fun y =>
          (∫ u in (0 : ℝ)..(1 : ℝ),
            ((Real.log (1 - u))⁻¹ + (Real.log (1 + u))⁻¹)) +
          ∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) := by
      apply Filter.eventuallyEq_of_mem hmem
      intro y hy
      have hy_gt : 1 < y := Set.mem_Ioi.mp hy
      exact Real.logarithmicIntegralReal_of_one_lt hy_gt
    have hD := hC.congr_of_eventuallyEq heq
    simpa [one_div] using hD

end Real
