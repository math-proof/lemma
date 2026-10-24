import Mathlib
import sympy.Basic
open MeasureTheory Real Filter Topology FourierTransform Complex


/-- ported from external source -/

private lemma  setIntegral_fourierChar_Icc (a t : ℝ) (ha : 0 ≤ a) (ht : t ≠ 0) :
  ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) =
    ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ) := by
  have hle : -a ≤ a := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hc : (-(2 * π * t) * I : ℂ) ≠ 0 := by
    apply mul_ne_zero _ I_ne_zero
    simp only [neg_ne_zero, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, false_or,
      not_or]
    exact ⟨Real.pi_ne_zero, ht⟩
  have hfun : (fun u : ℝ => ((𝐞 (-(t * u)) : Circle) : ℂ)) =
      fun u : ℝ => Complex.exp ((-(2 * π * t) * I) * (u : ℂ)) := by
    funext u
    rw [Real.fourierChar_apply]
    congr 1
    push_cast
    ring
  rw [hfun, integral_exp_mul_complex hc]
  have h1 : (-(2 * ↑π * ↑t) * I) * (a : ℂ) = -((2 * π * a * t : ℝ) : ℂ) * I := by push_cast; ring
  have h2 : (-(2 * ↑π * ↑t) * I) * ((-a : ℝ) : ℂ) = ((2 * π * a * t : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h1, h2]
  set θ : ℝ := 2 * π * a * t with hθ
  have hnum : Complex.exp (-(θ : ℂ) * I) - Complex.exp ((θ : ℂ) * I) =
      -2 * Complex.sin θ * I := by
    rw [show (-(θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I, exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hnum]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht
  push_cast
  field_simp

private lemma  setIntegral_fourier_Icc_eq (h : ℝ → ℂ) (hh : Integrable h) (a : ℝ) :
  ∫ u in Set.Icc (-a) a, 𝓕 h u =
    ∫ t, h t * ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) := by
  set g : ℝ → ℂ := (Set.Icc (-a) a).indicator (fun _ => (1 : ℂ)) with hg
  have hgi : Integrable g := by
    rw [hg, integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const measure_Icc_lt_top.ne
  have hF : (𝓕 h) = VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) h := rfl
  have hflip := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (f := h) (g := g) Real.continuous_fourierChar continuous_inner hh hgi
  have hL : ∫ u, (VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) h u) • g u =
      ∫ u in Set.Icc (-a) a, 𝓕 h u := by
    rw [← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    rw [hg, ← hF]
    if hu : u ∈ Set.Icc (-a) a then
      simp [Set.indicator_of_mem hu]
    else
      simp [Set.indicator_of_notMem hu]
  have hR : ∀ t : ℝ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ).flip g t =
      ∫ u in Set.Icc (-a) a, ((𝐞 (-(t * u)) : Circle) : ℂ) := by
    intro t
    rw [VectorFourier.fourierIntegral, ← integral_indicator measurableSet_Icc]
    congr 1
    funext u
    rw [LinearMap.flip_apply, innerₗ_apply_apply, RCLike.inner_apply, RCLike.conj_to_real,
      mul_comm u t, hg]
    if hu : u ∈ Set.Icc (-a) a then
      simp [Set.indicator_of_mem hu, Circle.smul_def, mul_comm]
    else
      simp [Set.indicator_of_notMem hu]
  rw [← hL, hflip]
  congr 1
  funext t
  rw [hR t, smul_eq_mul]

private lemma  setIntegral_fourier_Icc_eq_integral_sin (h : ℝ → ℂ) (hh : Integrable h) (a : ℝ)
  (ha : 0 ≤ a) :
  ∫ u in Set.Icc (-a) a, 𝓕 h u =
    ∫ t, h t * ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ) := by
  rw [setIntegral_fourier_Icc_eq h hh a]
  apply integral_congr_ae
  have h0 : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := by
    rw [compl_mem_ae_iff]
    apply measure_singleton 0
  filter_upwards [h0] with t ht
  have ht' : t ≠ 0 := ht
  rw [setIntegral_fourierChar_Icc a t ha ht']

private lemma  integral_fourier_eq (h : ℝ → ℂ) (hh : Integrable h) (hFh : Integrable (𝓕 h))
  (h0 : ContinuousAt h 0) : ∫ u, 𝓕 h u = h 0 := by
  have := hh.fourierInv_fourier_eq hFh h0
  rw [Real.fourierInv_eq] at this
  simpa using this

private lemma helper_main (h : ℝ → ℂ) (hh : Integrable h) (hFh : Integrable (𝓕 h)) (h0 : ContinuousAt h 0) :
  Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t) atTop
    (𝓝 ((π : ℂ) * h 0)) := by
  have hT : Tendsto (fun a : ℝ => ∫ u in (-a)..a, 𝓕 h u) atTop (𝓝 (h 0)) := by
    rw [← integral_fourier_eq h hh hFh h0]
    exact intervalIntegral_tendsto_integral hFh tendsto_neg_atTop_atBot tendsto_id
  have hT2 : Tendsto (fun a : ℝ => ∫ t, h t * ((Real.sin (2 * π * a * t) / (π * t) : ℝ) : ℂ))
      atTop (𝓝 (h 0)) := by
    refine hT.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      setIntegral_fourier_Icc_eq_integral_sin h hh a ha]
  have hsub : Tendsto (fun R : ℝ => R / (2 * π)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hT3 := hT2.comp hsub
  have hT4 : Tendsto (fun R : ℝ => ∫ t, h t * ((Real.sin (R * t) / (π * t) : ℝ) : ℂ))
      atTop (𝓝 (h 0)) := by
    refine hT3.congr ?_
    intro R
    simp only [Function.comp_apply]
    congr 1
    funext t
    congr 3
    field_simp
  have hT5 := hT4.const_mul (π : ℂ)
  refine hT5.congr ?_
  intro R
  rw [← integral_const_mul]
  congr 1
  funext t
  if ht : t = 0 then
    simp [ht]
  else
    have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
@[path]
private lemma main
-- given
  (h : ℝ → ℂ)
  (hh : MeasureTheory.Integrable h)
  (hFh : MeasureTheory.Integrable (𝓕 h))
  (h0 : ContinuousAt h 0) :
-- imply
  Filter.Tendsto (fun R : ℝ => ∫ t : ℝ, ((Real.sin (R * t) / t : ℝ) : ℂ) * h t)
      Filter.atTop (nhds ((Real.pi : ℂ) * h 0)) :=
-- proof
  helper_main h hh hFh h0


-- created on 2026-10-23
