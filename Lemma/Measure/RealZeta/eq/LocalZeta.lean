import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.LanglandsTunnell.ArchPlace
import Lemma.Int.P2MUtil

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace Metric
open scoped NNReal ENNReal Pointwise

/--
[LanglandsTunnell_TateLocal_realZeta_eq_localZeta](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.lean)
-/

private lemma  distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
  distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := closedBall (0:ℂ) 1) (μ := volume)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 from (mul_one _).symm,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

private lemma  modulus_complex_eq_nnnorm_sq : ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  ·
    rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

private lemma  distribHaarChar_real_eq_nnnorm (x : ℝˣ) :
  distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := closedBall (0:ℝ) 1) (μ := volume)
    (measure_closedBall_pos volume (0:ℝ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' x.ne_zero, smul_zero, mul_one,
    show ‖(x:ℝ)‖ = ‖(x:ℝ)‖ * 1 from (mul_one _).symm,
    Measure.addHaar_closedBall_mul volume (0:ℝ) (norm_nonneg _) zero_le_one,
    Module.finrank_self, pow_one]
  simp only [ofReal_norm, enorm_eq_nnnorm]

private lemma  modulus_real_eq_nnnorm : ∀ (x : ℝ), modulus x = ‖x‖₊ := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  ·
    rw [modulus_of_ne_zero hx, distribHaarChar_real_eq_nnnorm]
    simp

private lemma  integral_mulMeasure
  {K : Type*}
  [Field K]
  [TopologicalSpace K]
  [IsTopologicalRing K]
  [LocallyCompactSpace K]
  [MeasurableSpace K]
  [MeasurableSingletonClass K]
  (μ : Measure K) (F : K → ℂ)
  (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
  ∫ x, F x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set K), ((modulus x)⁻¹ : NNReal) • F x ∂μ := by
  have hae : (fun x : K => ((modulus x : ENNReal))⁻¹) =ᵐ[μ.restrict {0}ᶜ] fun x : K => (((modulus x)⁻¹ : NNReal) : ENNReal) := by
    refine (MeasureTheory.ae_restrict_iff' (MeasurableSet.singleton (0 : K)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    show ((modulus x : ENNReal))⁻¹ = (((modulus x)⁻¹ : NNReal) : ENNReal)
    rw [ENNReal.coe_inv (modulus_ne_zero hx0)]
  rw [mulMeasure, MeasureTheory.withDensity_congr_ae hae,
    integral_withDensity_eq_integral_smul₀ hm]

private lemma  complexZeta_eq_localZeta_impl (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ)
  (hm : AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ)) :
  complexZeta μ f χ s = localZeta μ f χ s := by
  rw [localZeta, integral_mulMeasure μ _ hm, complexZeta]
  rw [← MeasureTheory.integral_indicator (MeasurableSet.singleton (0:ℂ)).compl]
  congr 1
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  ·
    rw [Set.indicator_of_mem (show z ∈ ({0}ᶜ : Set ℂ) by simpa using hz)]
    have hmz : modulus z = ‖z‖₊ ^ 2 := modulus_complex_eq_nnnorm_sq z
    have hnz : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [NNReal.smul_def, Complex.real_smul, hmz]
    rw [show (f z * charExt χ z * (‖z‖ : ℂ) ^ (2 * s - 2) : ℂ) = (f z * charExt χ z) * ((‖z‖ : ℂ) ^ (2 * s - 2)) from by ring,
       show ((((‖z‖₊ ^ 2)⁻¹ : NNReal) : ℝ) : ℂ) * (f z * charExt χ z * ((((‖z‖₊^2 : NNReal) : ℝ) : ℂ)) ^ s) = (f z * charExt χ z) * (((((‖z‖₊^2 : NNReal)⁻¹ : NNReal) : ℝ) : ℂ)
              * ((((‖z‖₊^2 : NNReal) : ℝ) : ℂ)) ^ s) from by ring]
    congr 1
    have hsq : ((((‖z‖₊^2 : NNReal) : ℝ) : ℂ)) = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := by
      push_cast; ring
    have h1 : ((((‖z‖₊^2 : NNReal) : ℝ) : ℂ))^s = (‖z‖ : ℂ)^((2:ℂ)*s) := by
      rw [hsq, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
        ← Complex.cpow_add _ _ hnz]; ring_nf
    have h2 : ((((‖z‖₊^2 : NNReal)⁻¹ : NNReal) : ℝ) : ℂ) = (‖z‖ : ℂ)^(-(2:ℂ)) := by
      rw [show (-(2:ℂ)) = (-1) + (-1) from by ring, Complex.cpow_add _ _ hnz,
        Complex.cpow_neg_one]
      push_cast; ring
    rw [h1, h2, ← Complex.cpow_add _ _ hnz]
    ring_nf

private lemma  realZeta_eq_localZeta_impl (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ)
  (hm : AEMeasurable (fun x : ℝ => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
  realZeta μ f χ s = localZeta μ f χ s := by
  rw [localZeta, integral_mulMeasure μ _ hm, realZeta]
  rw [← MeasureTheory.integral_indicator (MeasurableSet.singleton (0:ℝ)).compl]
  congr 1
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  ·
    rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set ℝ) by simpa using hx)]
    have hmx : modulus x = ‖x‖₊ := modulus_real_eq_nnnorm x
    have hnz : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
    simp only [NNReal.smul_def, Complex.real_smul, hmx]
    rw [show (f x * charExt χ x * (‖x‖ : ℂ) ^ (s - 1) : ℂ) = (f x * charExt χ x) * ((‖x‖ : ℂ) ^ (s - 1)) from by ring,
       show ((((‖x‖₊)⁻¹ : NNReal) : ℝ) : ℂ) * (f x * charExt χ x * (((‖x‖₊ : ℝ) : ℂ)) ^ s) = (f x * charExt χ x) * ((((‖x‖₊⁻¹ : NNReal) : ℝ) : ℂ) * (((‖x‖₊ : ℝ) : ℂ)) ^ s) from by ring]
    congr 1
    have h2 : ((((‖x‖₊)⁻¹ : NNReal) : ℝ) : ℂ) = (‖x‖ : ℂ)^(-(1:ℂ)) := by
      push_cast; rw [Complex.cpow_neg, Complex.cpow_one]
    rw [h2, show (((‖x‖₊ : ℝ) : ℂ)) = (‖x‖ : ℂ) from by push_cast; ring,
      ← Complex.cpow_add _ _ hnz]
    ring_nf

private lemma  hm_complex_any (μ : Measure ℂ) :
  AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ) := by
  have heq : (fun z : ℂ => (modulus z)⁻¹) = fun z => (‖z‖₊ ^ 2)⁻¹ :=
    funext fun z => by rw [modulus_complex_eq_nnnorm_sq]
  rw [heq]
  exact ((measurable_nnnorm.pow_const 2).inv).aemeasurable

private lemma  hm_real_any (μ : Measure ℝ) :
  AEMeasurable (fun x : ℝ => (modulus x)⁻¹) (μ.restrict {0}ᶜ) := by
  have heq : (fun x : ℝ => (modulus x)⁻¹) = fun x => (‖x‖₊)⁻¹ :=
    funext fun x => by rw [modulus_real_eq_nnnorm]
  rw [heq]
  exact (measurable_nnnorm.inv).aemeasurable

private lemma  complexZeta_eq_localZeta_unc (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
  complexZeta μ f χ s = localZeta μ f χ s :=
  complexZeta_eq_localZeta_impl μ f χ s (hm_complex_any μ)

private lemma  realZeta_eq_localZeta_unc (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) :
  realZeta μ f χ s = localZeta μ f χ s :=
  realZeta_eq_localZeta_impl μ f χ s (hm_real_any μ)
@[path]
private lemma main
  {μ : Measure ℝ}
  {f : ℝ → ℂ}
  {χ : ℝˣ →* ℂˣ}
  {s : ℂ} :
-- imply
  realZeta μ f χ s = localZeta μ f χ s :=
-- proof
  realZeta_eq_localZeta_unc μ f χ s


-- created on 2026-10-23
