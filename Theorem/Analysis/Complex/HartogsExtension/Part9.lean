/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Def.Analysis.Complex.HartogsExtension.Part8


namespace Complex.HartogsWanted

open MeasureTheory Set

open scoped Convolution

theorem hartogsextUnitCircle_ne_zero (θ : ℝ) : hartogsextUnitCircle θ ≠ 0 := by
  rw [← norm_ne_zero_iff]
  simp [hartogsextUnitCircle, Complex.norm_cos_add_sin_mul_I]

theorem hartogsext_barDeriv_polar_identity
    (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) (hr : r ≠ 0) :
    (hartogsextUnitCircle θ)⁻¹ *
        ((2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I)) =
      (2 : ℂ)⁻¹ *
        (L (hartogsextUnitCircle θ) +
          Complex.I * (r : ℂ)⁻¹ *
            L ((r : ℂ) * Complex.I * hartogsextUnitCircle θ)) := by
  let c := Real.cos θ
  let s := Real.sin θ
  let e := hartogsextUnitCircle θ
  have heq : e = c • (1 : ℂ) + s • Complex.I := by
    simp [e, c, s, hartogsextUnitCircle, RCLike.real_smul_eq_coe_mul]
  have hIeq : Complex.I * e = (-s) • (1 : ℂ) + c • Complex.I := by
    rw [heq]
    simp only [mul_add, mul_smul_comm, Complex.I_mul_I, mul_one, smul_neg]
    simp only [RCLike.real_smul_eq_coe_mul]
    push_cast
    ring
  have hLe : L e = c • L 1 + s • L Complex.I := by
    rw [heq, map_add, map_smul, map_smul]
  have hLrIe : L ((r : ℂ) * Complex.I * e) =
      r • ((-s) • L 1 + c • L Complex.I) := by
    have hrIe : (r : ℂ) * Complex.I * e = r • (Complex.I * e) := by
      simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
    rw [hrIe, map_smul, hIeq, map_add, map_smul, map_smul]
  have heinv : e⁻¹ = (c : ℂ) - s * Complex.I := by
    have heexp : e = Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I]
      simp [e, hartogsextUnitCircle]
    rw [heexp, ← Complex.exp_neg]
    rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by
      push_cast
      ring]
    rw [Complex.exp_mul_I]
    dsimp [c, s]
    simp [sub_eq_add_neg]
  rw [hLe, hLrIe]
  rw [heinv]
  simp only [RCLike.real_smul_eq_coe_mul]
  push_cast
  field_simp [hr]
  ring_nf
  rw [Complex.I_sq]
  ring_nf
  simp only [sub_eq_add_neg]
  ac_rfl

theorem hartogsext_barDeriv_polar_identity'
    (L : ℂ →L[ℝ] ℂ) (r θ : ℝ) (hr : r ≠ 0) :
    (hartogsextUnitCircle θ)⁻¹ *
        ((2 : ℂ)⁻¹ * (L 1 + Complex.I * L Complex.I)) =
      (2 : ℂ)⁻¹ *
        (L (hartogsextUnitCircle θ) +
          Complex.I * L (Complex.I * hartogsextUnitCircle θ)) := by
  rw [hartogsext_barDeriv_polar_identity L r θ hr]
  congr 2
  have hinput : (r : ℂ) * Complex.I * hartogsextUnitCircle θ =
      r • (Complex.I * hartogsextUnitCircle θ) := by
    simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
  rw [hinput, map_smul]
  simp only [RCLike.real_smul_eq_coe_mul]
  field_simp [hr]
  rfl

theorem hartogsext_hasDerivAt_polar_radius
    {h : ℂ → ℂ} (hh : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun ρ : ℝ ↦ h ((ρ : ℂ) * hartogsextUnitCircle θ))
      (fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) r := by
  have hin : HasDerivAt (fun ρ : ℝ ↦ (ρ : ℂ) * hartogsextUnitCircle θ)
      (hartogsextUnitCircle θ) r := by
    convert ((hasDerivAt_id (𝕜 := ℝ) (x := r)).smul_const
      (hartogsextUnitCircle θ)) using 1 <;> simp [RCLike.real_smul_eq_coe_mul]
  exact (hh ((r : ℂ) * hartogsextUnitCircle θ)).hasFDerivAt.comp_hasDerivAt r hin

theorem hartogsext_hasDerivAt_polar_angle
    {h : ℂ → ℂ} (hh : Differentiable ℝ h) (r θ : ℝ) :
    HasDerivAt (fun φ : ℝ ↦ h ((r : ℂ) * hartogsextUnitCircle φ))
      (fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        ((r : ℂ) * Complex.I * hartogsextUnitCircle θ)) θ := by
  have hcircle : (fun φ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle φ) = circleMap 0 r := by
    funext φ
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
  have hin : HasDerivAt (fun φ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle φ)
      ((r : ℂ) * Complex.I * hartogsextUnitCircle θ) θ := by
    rw [hcircle]
    convert hasDerivAt_circleMap 0 r θ using 1
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
    ring
  exact (hh ((r : ℂ) * hartogsextUnitCircle θ)).hasFDerivAt.comp_hasDerivAt θ hin

theorem hartogsext_integral_inv_mul_barDeriv_eq_polar (h : ℂ → ℂ) :
    (∫ z : ℂ, z⁻¹ * barDeriv h z) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (hartogsextUnitCircle p.2)⁻¹ *
          barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2) := by
  rw [← Complex.integral_comp_polarCoord_symm (fun z : ℂ ↦ z⁻¹ * barDeriv h z)]
  change (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
    p.1 • ((Complex.polarCoord.symm p)⁻¹ * barDeriv h (Complex.polarCoord.symm p))) = _
  apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  simp only [Complex.polarCoord_symm_apply]
  change (p.1 : ℂ) *
      (((p.1 : ℂ) * hartogsextUnitCircle p.2)⁻¹ *
        barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) =
    (hartogsextUnitCircle p.2)⁻¹ *
      barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
  have hp1 : (0 : ℝ) < p.1 := Set.mem_Ioi.mp hp.1
  field_simp [ne_of_gt hp1, hartogsextUnitCircle_ne_zero]

theorem hartogsext_integrableOn_polar_fderiv
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h)
    {v : ℝ → ℂ} (hv : Continuous v) :
    IntegrableOn
      (fun p : ℝ × ℝ ↦ fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (v p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  let φ : ℝ × ℝ → ℂ := fun p ↦
    fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (v p.2)
  have hDf : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have hpoint : Continuous (fun p : ℝ × ℝ ↦
      (p.1 : ℂ) * hartogsextUnitCircle p.2) := by
    unfold hartogsextUnitCircle
    fun_prop
  have hφ : Continuous φ :=
    (hDf.comp hpoint).clm_apply (hv.comp continuous_snd)
  obtain ⟨R, hRpos, hR⟩ := hhc.isCompact.isBounded.exists_pos_norm_lt
  let q : Set (ℝ × ℝ) := Set.Icc 0 R ×ˢ Set.Icc (-Real.pi) Real.pi
  have hq : IsCompact q := isCompact_Icc.prod isCompact_Icc
  have hφq : IntegrableOn φ q := hφ.continuousOn.integrableOn_compact hq
  have hind : Integrable (q.indicator φ) := hφq.integrable_indicator hq.measurableSet
  apply hind.integrableOn.congr_fun _ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  by_cases hpR : p.1 ≤ R
  · rw [Set.indicator_of_mem]
    exact ⟨⟨hp.1.le, hpR⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  · rw [Set.indicator_of_notMem]
    · dsimp [φ]
      have hz : (p.1 : ℂ) * hartogsextUnitCircle p.2 ∉ tsupport h := by
        intro hz
        have hnorm := hR _ hz
        have heq : ‖(p.1 : ℂ) * hartogsextUnitCircle p.2‖ = p.1 := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp.1]
          simp [hartogsextUnitCircle, Complex.norm_cos_add_sin_mul_I]
        rw [heq] at hnorm
        exact hpR hnorm.le
      rw [fderiv_of_notMem_tsupport ℝ hz]
      simp
    · intro hpq
      exact hpR hpq.1.2

theorem hartogsext_integral_polar_radius
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) (θ : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
      fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) =
        -h 0 := by
  let q : ℝ → ℂ := fun r ↦ h ((r : ℂ) * hartogsextUnitCircle θ)
  have hline : ContDiff ℝ 1 (fun r : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) := by
    simpa [RCLike.real_smul_eq_coe_mul] using
      (contDiff_id.smul_const (hartogsextUnitCircle θ) :
        ContDiff ℝ 1 (fun r : ℝ ↦ r • hartogsextUnitCircle θ))
  have hq : ContDiff ℝ 1 q := by
    simpa only [q, Function.comp_def] using hh.comp hline
  obtain ⟨R, hRpos, hR⟩ := hhc.isCompact.isBounded.exists_pos_norm_lt
  have hqc : HasCompactSupport q := by
    refine HasCompactSupport.of_support_subset_isCompact
      (show IsCompact (Set.Icc (-R) R) from isCompact_Icc) ?_
    intro r hr
    have hz : (r : ℂ) * hartogsextUnitCircle θ ∈ tsupport h :=
      subset_closure hr
    have hnorm := hR _ hz
    have habs : |r| < R := by
      simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs, hartogsextUnitCircle,
        Complex.norm_cos_add_sin_mul_I] using hnorm
    exact ⟨(neg_lt_of_abs_lt habs).le, (lt_of_abs_lt habs).le⟩
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ) (hartogsextUnitCircle θ)) =
      ∫ r in Set.Ioi (0 : ℝ), deriv q r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact (hartogsext_hasDerivAt_polar_radius (hh.differentiable (by norm_num)) r θ).deriv.symm
    _ = -q 0 := hqc.integral_Ioi_deriv_eq hq 0
    _ = -h 0 := by simp [q]

theorem hartogsext_integral_polar_angle
    {h : ℂ → ℂ} (hh : ContDiff ℝ 1 h) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        (Complex.I * hartogsextUnitCircle θ)) = 0 := by
  let q : ℝ → ℂ := fun θ ↦ h ((r : ℂ) * hartogsextUnitCircle θ)
  have hcircle : (fun θ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) = circleMap 0 r := by
    funext θ
    simp [circleMap, hartogsextUnitCircle, Complex.exp_mul_I]
  have hinner : ContDiff ℝ 1 (fun θ : ℝ ↦ (r : ℂ) * hartogsextUnitCircle θ) := by
    rw [hcircle]
    exact contDiff_circleMap 0 r
  have hq : ContDiff ℝ 1 q := by
    simpa only [q, Function.comp_def] using hh.comp hinner
  have hderiv (θ : ℝ) : deriv q θ =
      fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
        ((r : ℂ) * Complex.I * hartogsextUnitCircle θ) :=
    (hartogsext_hasDerivAt_polar_angle (hh.differentiable (by norm_num)) r θ).deriv
  have hrewrite (θ : ℝ) :
      Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
          (Complex.I * hartogsextUnitCircle θ) =
        (Complex.I * (r : ℂ)⁻¹) * deriv q θ := by
    rw [hderiv]
    have hinput : (r : ℂ) * Complex.I * hartogsextUnitCircle θ =
        r • (Complex.I * hartogsextUnitCircle θ) := by
      simp [RCLike.real_smul_eq_coe_mul, mul_assoc]
    rw [hinput, map_smul]
    simp only [RCLike.real_smul_eq_coe_mul]
    field_simp [hr.ne']
    exact mul_comm _ _
  calc
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        Complex.I * fderiv ℝ h ((r : ℂ) * hartogsextUnitCircle θ)
          (Complex.I * hartogsextUnitCircle θ)) =
      ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        (Complex.I * (r : ℂ)⁻¹) * deriv q θ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          exact hrewrite θ
    _ = (Complex.I * (r : ℂ)⁻¹) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, deriv q θ := by
      rw [integral_const_mul]
    _ = (Complex.I * (r : ℂ)⁻¹) *
        ∫ θ in (-Real.pi)..Real.pi, deriv q θ := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    _ = (Complex.I * (r : ℂ)⁻¹) * (q Real.pi - q (-Real.pi)) := by
      rw [intervalIntegral.integral_deriv_of_contDiffOn_Icc hq.contDiffOn
        (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    _ = 0 := by
      simp [q, hartogsextUnitCircle]

theorem hartogsext_integral_inv_mul_barDeriv
    {h : ℂ → ℂ} (hhc : HasCompactSupport h) (hh : ContDiff ℝ 1 h) :
    (∫ z : ℂ, z⁻¹ * barDeriv h z) = -(Real.pi : ℂ) * h 0 := by
  let radial : ℝ × ℝ → ℂ := fun p ↦
    fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2) (hartogsextUnitCircle p.2)
  let angular : ℝ × ℝ → ℂ := fun p ↦
    Complex.I * fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
      (Complex.I * hartogsextUnitCircle p.2)
  have hunit : Continuous hartogsextUnitCircle := by
    unfold hartogsextUnitCircle
    fun_prop
  have hradial : IntegrableOn radial
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    exact hartogsext_integrableOn_polar_fderiv hhc hh hunit
  have hangbase : IntegrableOn
      (fun p : ℝ × ℝ ↦ fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)
        (Complex.I * hartogsextUnitCircle p.2))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
    apply hartogsext_integrableOn_polar_fderiv hhc hh
      (v := fun θ ↦ Complex.I * hartogsextUnitCircle θ)
    exact continuous_const.mul hunit
  have hangular : IntegrableOn angular
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) :=
    hangbase.const_mul Complex.I
  have hradialIntegral :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) =
        -(2 * Real.pi : ℝ) * h 0 := by
    calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) =
          ∫ p in Set.Ioo (-Real.pi) Real.pi ×ˢ Set.Ioi (0 : ℝ), radial p.swap :=
        (setIntegral_prod_swap (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi) radial).symm
      _ = ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ∫ r in Set.Ioi (0 : ℝ), radial (r, θ) := by
        simpa only [Measure.volume_eq_prod, Function.comp_apply,
          Prod.swap_prod_mk] using
          (setIntegral_prod (radial ∘ Prod.swap) hradial.swap)
      _ = ∫ _θ in Set.Ioo (-Real.pi) Real.pi, -h 0 := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ hθ
        exact hartogsext_integral_polar_radius hhc hh θ
      _ = -(2 * Real.pi : ℝ) * h 0 := by
        have hpi : 0 ≤ Real.pi - -Real.pi := by linarith [Real.pi_pos]
        have hlength : Real.pi - -Real.pi = 2 * Real.pi := by ring
        rw [integral_const]
        simp only [Measure.restrict_apply_univ, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal hpi, RCLike.real_smul_eq_coe_mul]
        rw [hlength]
        push_cast
        rw [neg_mul, mul_neg]
        rfl
  have hangularIntegral :
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) = 0 := by
    calc
      (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) =
          ∫ r in Set.Ioi (0 : ℝ),
            ∫ θ in Set.Ioo (-Real.pi) Real.pi, angular (r, θ) := by
        simpa only [Measure.volume_eq_prod] using
          (setIntegral_prod angular hangular)
      _ = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro r hr
        exact hartogsext_integral_polar_angle hh hr
  rw [hartogsext_integral_inv_mul_barDeriv_eq_polar]
  calc
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (hartogsextUnitCircle p.2)⁻¹ *
          barDeriv h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) =
      ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        (2 : ℂ)⁻¹ * (radial p + angular p) := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      exact hartogsext_barDeriv_polar_identity'
        (fderiv ℝ h ((p.1 : ℂ) * hartogsextUnitCircle p.2)) p.1 p.2
          (ne_of_gt hp.1)
    _ = (2 : ℂ)⁻¹ *
        ((∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, radial p) +
          ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi, angular p) := by
      rw [integral_const_mul, integral_add hradial hangular]
    _ = -(Real.pi : ℂ) * h 0 := by
      rw [hradialIntegral, hangularIntegral]
      push_cast
      ring

theorem hartogsext_barDeriv_const_sub
    {g : ℂ → ℂ} (hg : Differentiable ℝ g) (z t : ℂ) :
    barDeriv (fun w ↦ g (z - w)) t = -barDeriv g (z - t) := by
  have hinner : HasFDerivAt (fun w : ℂ ↦ z - w) (-(1 : ℂ →L[ℝ] ℂ)) t :=
    (hasFDerivAt_id t).const_sub z
  have hcomp := (hg (z - t)).hasFDerivAt.comp t hinner
  have hcomp' : HasFDerivAt (fun w ↦ g (z - w))
      (fderiv ℝ g (z - t) ∘L (-(1 : ℂ →L[ℝ] ℂ))) t := by
    apply hcomp.congr_of_eventuallyEq
    filter_upwards with w
    rfl
  rw [barDeriv, barDeriv, hcomp'.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, one_apply_eq_self, map_neg]
  ring

theorem hartogsext_integral_inv_mul_barDeriv_const_sub
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    (∫ t : ℂ, t⁻¹ * barDeriv g (z - t)) = (Real.pi : ℂ) * g z := by
  let h : ℂ → ℂ := fun t ↦ g (z - t)
  have hhc : HasCompactSupport h := by
    simpa only [h, Function.comp_def, Homeomorph.subLeft,
      Homeomorph.homeomorph_mk_coe, Equiv.subLeft_apply] using
      hgc.comp_homeomorph (Homeomorph.subLeft z)
  have hh : ContDiff ℝ 1 h := by
    have hinner : ContDiff ℝ 1 (fun t : ℂ ↦ z - t) :=
      contDiff_const.sub contDiff_id
    simpa only [h, Function.comp_def] using hg.comp hinner
  have hcore := hartogsext_integral_inv_mul_barDeriv hhc hh
  calc
    (∫ t : ℂ, t⁻¹ * barDeriv g (z - t)) =
        -(∫ t : ℂ, t⁻¹ * barDeriv h t) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with t
      rw [hartogsext_barDeriv_const_sub (hg.differentiable (by norm_num))]
      ring
    _ = -(-(Real.pi : ℂ) * h 0) := by rw [hcore]
    _ = (Real.pi : ℂ) * g z := by simp [h]

theorem hartogsext_barDeriv_cauchyGreenTransform_eq
    {g : ℂ → ℂ} (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    barDeriv (hartogsextCauchyGreenTransform g) z = g z := by
  rw [hartogsext_barDeriv_cauchyGreenTransform hgc hg]
  simp only [convolution_def, hartogsextCauchyGreenKernel]
  calc
    (∫ t : ℂ, ((Real.pi : ℂ)⁻¹ * t⁻¹) * barDeriv g (z - t)) =
        (Real.pi : ℂ)⁻¹ * ∫ t : ℂ, t⁻¹ * barDeriv g (z - t) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ac_rfl
    _ = g z := by
      rw [hartogsext_integral_inv_mul_barDeriv_const_sub hgc hg z]
      field_simp [ne_of_gt Real.pi_pos]

/-- A compactly supported `C¹` function on `ℂ` is a Wirtinger derivative. -/
theorem exists_differentiable_barDeriv_eq_of_hasCompactSupport
    {g : ℂ → ℂ} (hg : Differentiable ℝ g) (hDg : Continuous (fderiv ℝ g))
    (hgc : HasCompactSupport g) :
    ∃ u : ℂ → ℂ, Differentiable ℝ u ∧ ∀ z, barDeriv u z = g z := by
  have hg' : ContDiff ℝ 1 g := contDiff_one_iff_fderiv.mpr ⟨hg, hDg⟩
  refine ⟨hartogsextCauchyGreenTransform g, ?_, ?_⟩
  · intro z
    exact (hartogsext_cauchyGreenTransform_hasFDerivAt hgc hg' z).differentiableAt
  · exact hartogsext_barDeriv_cauchyGreenTransform_eq hgc hg'

theorem hartogsext_barPartial_partialCauchyGreen_self
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    (x : EuclideanSpace ℂ (Fin n)) :
    hartogsextBarPartial i (hartogsextPartialCauchyGreen i g) x = g x := by
  have hsc := hartogsext_hasCompactSupport_slice hgc i x
  have hsd := hartogsext_contDiff_slice hg i x
  have hfun : barDeriv (hartogsextSlice i g x) =
      hartogsextSlice i (hartogsextBarPartial i g) x := by
    funext z
    exact hartogsext_barDeriv_slice hg i x z
  calc
    hartogsextBarPartial i (hartogsextPartialCauchyGreen i g) x =
        hartogsextPartialCauchyGreen i (hartogsextBarPartial i g) x :=
      hartogsext_barPartial_partialCauchyGreen hgc hg i i x
    _ = (hartogsextCauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
          barDeriv (hartogsextSlice i g x)) (WithLp.ofLp x i) := by
      unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
      rw [hfun]
    _ = barDeriv (hartogsextCauchyGreenTransform (hartogsextSlice i g x))
        (WithLp.ofLp x i) :=
      (hartogsext_barDeriv_cauchyGreenTransform hsc hsd _).symm
    _ = hartogsextSlice i g x (WithLp.ofLp x i) :=
      hartogsext_barDeriv_cauchyGreenTransform_eq hsc hsd _
    _ = g x := by
      unfold hartogsextSlice
      rw [hartogsextReplace_self]

theorem hartogsext_partialCauchyGreen_eq_zero_of_coord
    {n : ℕ} {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (i j : Fin n) (hji : j ≠ i) {R : ℝ}
    (hR : ∀ y ∈ tsupport g, ‖y‖ < R)
    {x : EuclideanSpace ℂ (Fin n)} (hx : R ≤ ‖WithLp.ofLp x j‖) :
    hartogsextPartialCauchyGreen i g x = 0 := by
  unfold hartogsextPartialCauchyGreen hartogsextCauchyGreenTransform
  simp only [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  rw [ContinuousLinearMap.mul_apply']
  have hslice :
      hartogsextSlice i g x (WithLp.ofLp x i - t) = 0 := by
    apply Classical.byContradiction
    intro hne
    have hy : hartogsextReplace i x (WithLp.ofLp x i - t) ∈ tsupport g :=
      subset_tsupport g hne
    have hcoord := PiLp.norm_apply_le
      (hartogsextReplace i x (WithLp.ofLp x i - t)) j
    have heq : WithLp.ofLp (hartogsextReplace i x
        (WithLp.ofLp x i - t)) j = WithLp.ofLp x j := by
      simp [hartogsextReplace, hji]
    rw [heq] at hcoord
    exact (not_lt_of_ge hx) (hcoord.trans_lt (hR _ hy))
  simp [hslice]

theorem hartogsext_hasCompactSupport_partialCauchyGreen
    {n : ℕ} (hn : 2 ≤ n)
    {g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hgc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (i : Fin n)
    {h : Fin n → EuclideanSpace ℂ (Fin n) → ℂ}
    (hhc : ∀ j, HasCompactSupport (h j))
    (hbar : ∀ j x,
      hartogsextBarPartial j (hartogsextPartialCauchyGreen i g) x = h j x) :
    HasCompactSupport (hartogsextPartialCauchyGreen i g) := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  obtain ⟨Rg, hRg_pos, hRg⟩ := hgc.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨Rh, hRh_pos, hRh⟩ := (hhc j).isCompact.isBounded.exists_pos_norm_lt
  let u := hartogsextPartialCauchyGreen i g
  have hu : ContDiff ℝ 1 u := hartogsext_contDiff_partialCauchyGreen hgc hg i
  have htransverse {x : EuclideanSpace ℂ (Fin n)} {k : Fin n}
      (hki : k ≠ i) (hx : Rg ≤ ‖WithLp.ofLp x k‖) : u x = 0 := by
    exact hartogsext_partialCauchyGreen_eq_zero_of_coord i k hki hRg hx
  have hfirst {x : EuclideanSpace ℂ (Fin n)}
      (hx : Rh ≤ ‖WithLp.ofLp x i‖) : u x = 0 := by
    let q : ℂ → ℂ := hartogsextSlice j u x
    have hq_contDiff : ContDiff ℝ 1 q := hartogsext_contDiff_slice hu j x
    have hq_bar (z : ℂ) : barDeriv q z = 0 := by
      rw [show barDeriv q z =
        hartogsextBarPartial j u (hartogsextReplace j x z) by
          exact hartogsext_barDeriv_slice hu j x z]
      rw [hbar]
      apply Classical.byContradiction
      intro hne
      have hy : hartogsextReplace j x z ∈ tsupport (h j) :=
        subset_tsupport (h j) hne
      have hcoord := PiLp.norm_apply_le (hartogsextReplace j x z) i
      have heq : WithLp.ofLp (hartogsextReplace j x z) i = WithLp.ofLp x i := by
        simp [hartogsextReplace, Ne.symm hji]
      rw [heq] at hcoord
      exact (not_lt_of_ge hx) (hcoord.trans_lt (hRh _ hy))
    have hq_diff : Differentiable ℂ q := by
      intro z
      exact differentiableAt_of_barDeriv_eq_zero
        (hq_contDiff.differentiable (by norm_num) z) (hq_bar z)
    let z₀ : ℂ := ((Rg + 1 : ℝ) : ℂ)
    have hz₀ : Rg < ‖z₀‖ := by
      change Rg < ‖((Rg + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have hevent : Filter.EventuallyEq (nhds z₀) q (fun _ ↦ 0) := by
      have hopen : IsOpen {z : ℂ | Rg < ‖z‖} :=
        isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hz₀] with z hz
      apply htransverse hji
      simpa only [q, hartogsextReplace_apply] using hz.le
    have hq_an : AnalyticOnNhd ℂ q Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hq_diff
    have hq_zero : q = fun _ ↦ 0 :=
      hq_an.eq_of_eventuallyEq analyticOnNhd_const hevent
    have hself := congrFun hq_zero (WithLp.ofLp x j)
    simpa only [q, hartogsextSlice, hartogsextReplace_self] using hself
  let R : ℝ := max Rg Rh
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) ((n : ℝ) * R))
  intro x hx_support
  have hcoord (k : Fin n) : ‖WithLp.ofLp x k‖ ≤ R := by
    by_cases hki : k = i
    · subst k
      by_contra hxR
      have hzero := hfirst ((le_max_right Rg Rh).trans (le_of_not_ge hxR))
      exact hx_support hzero
    · by_contra hxR
      have hzero := htransverse hki
        ((le_max_left Rg Rh).trans (le_of_not_ge hxR))
      exact hx_support hzero
  rw [Metric.mem_closedBall, dist_zero_right]
  have hx_repr : x = ∑ k : Fin n,
      WithLp.ofLp x k • EuclideanSpace.single k 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.sum_repr x).symm
  calc
    ‖x‖ = ‖∑ k : Fin n,
        WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)‖ :=
      congrArg norm hx_repr
    _ ≤ ∑ k : Fin n,
        ‖WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)‖ := by
      simpa only [Finset.sum_filter] using
        (norm_sum_le Finset.univ (fun k : Fin n ↦
          WithLp.ofLp x k • EuclideanSpace.single k (1 : ℂ)))
    _ = ∑ k : Fin n, ‖WithLp.ofLp x k‖ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one]
    _ ≤ ∑ _k : Fin n, R := Finset.sum_le_sum fun k hk ↦ hcoord k
    _ = (n : ℝ) * R := by simp

theorem hartogsext_eqOn_of_differentiableOn_of_isConnected
    {n : ℕ} {s : Set (EuclideanSpace ℂ (Fin n))}
    {f g : EuclideanSpace ℂ (Fin n) → ℂ}
    (hs_open : IsOpen s) (hs_conn : IsConnected s)
    (hf : DifferentiableOn ℂ f s) (hg : DifferentiableOn ℂ g s)
    {x₀ : EuclideanSpace ℂ (Fin n)} (hx₀ : x₀ ∈ s)
    (hfg : Filter.EventuallyEq (nhds x₀) f g) : Set.EqOn f g s := by
  set A : Set (EuclideanSpace ℂ (Fin n)) :=
    {x | ∃ o : Set (EuclideanSpace ℂ (Fin n)),
      IsOpen o ∧ x ∈ o ∧ Set.EqOn f g o} with hA
  have hA_open : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨o, ho, hxo, heq⟩ := hx
    exact ⟨o, fun y hy ↦ ⟨o, ho, hy, heq⟩, ho, hxo⟩
  have hx₀A : x₀ ∈ A := by
    have hfg' : {x | f x = g x} ∈ nhds x₀ := hfg
    obtain ⟨o, ho_sub, ho_open, hx₀o⟩ := mem_nhds_iff.mp hfg'
    exact ⟨o, ho_open, hx₀o, fun x hx ↦ ho_sub hx⟩
  have hclosure : closure A ∩ s ⊆ A := by
    intro x hx
    obtain ⟨r, hr, hr_sub⟩ := Metric.isOpen_iff.mp hs_open x hx.2
    obtain ⟨y, hy_ball, hyA⟩ :=
      mem_closure_iff_nhds.mp hx.1 (Metric.ball x r)
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    obtain ⟨o, ho_open, hyo, heq_o⟩ := hyA
    refine ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_⟩
    intro z hz
    let v : EuclideanSpace ℂ (Fin n) := z - y
    let ℓ : ℂ → EuclideanSpace ℂ (Fin n) := fun t ↦ y + t • v
    have hℓ0 : ℓ 0 = y := by simp [ℓ]
    have hℓ1 : ℓ 1 = z := by simp [ℓ, v]
    have hℓ_diff : Differentiable ℂ ℓ := by
      exact (differentiable_id.smul_const v).const_add y
    have hℓ_cont : Continuous ℓ := hℓ_diff.continuous
    let D : Set ℂ := ℓ ⁻¹' Metric.ball x r
    have hD_open : IsOpen D := Metric.isOpen_ball.preimage hℓ_cont
    have h0D : (0 : ℂ) ∈ D := by
      change ℓ 0 ∈ Metric.ball x r
      rw [hℓ0]
      exact hy_ball
    have h1D : (1 : ℂ) ∈ D := by
      change ℓ 1 ∈ Metric.ball x r
      rw [hℓ1]
      exact hz
    have hD_convex : Convex ℝ D := by
      intro a ha b hb u w hu hw huw
      change ℓ (u • a + w • b) ∈ Metric.ball x r
      have haff : ℓ (u • a + w • b) = u • ℓ a + w • ℓ b := by
        simp only [ℓ]
        rw [smul_add, smul_add, add_smul, ← smul_assoc u a v,
          ← smul_assoc w b v]
        have hrearr :
            (u • y + (u • a) • v) + (w • y + (w • b) • v) =
              (u • y + w • y) + ((u • a) • v + (w • b) • v) := by
          abel
        rw [hrearr, ← add_smul u w y, huw, one_smul]
      rw [haff]
      exact (convex_ball x r) ha hb hu hw huw
    have hmaps : MapsTo ℓ D s := fun t ht ↦ hr_sub ht
    have hf_slice : DifferentiableOn ℂ (f ∘ ℓ) D :=
      hf.comp (hℓ_diff.differentiableOn (s := D)) hmaps
    have hg_slice : DifferentiableOn ℂ (g ∘ ℓ) D :=
      hg.comp (hℓ_diff.differentiableOn (s := D)) hmaps
    have hf_an : AnalyticOnNhd ℂ (f ∘ ℓ) D := hf_slice.analyticOnNhd hD_open
    have hg_an : AnalyticOnNhd ℂ (g ∘ ℓ) D := hg_slice.analyticOnNhd hD_open
    have hevent : Filter.EventuallyEq (nhds (0 : ℂ)) (f ∘ ℓ) (g ∘ ℓ) := by
      have htend : Filter.Tendsto ℓ (nhds (0 : ℂ)) (nhds y) := by
        simpa only [hℓ0] using hℓ_cont.tendsto 0
      filter_upwards [htend.eventually (ho_open.mem_nhds hyo)] with t ht
      exact heq_o ht
    have heqD := hf_an.eqOn_of_preconnected_of_eventuallyEq hg_an
      hD_convex.isPreconnected h0D hevent
    simpa only [Function.comp_apply, hℓ1] using heqD h1D
  let T : Set s := Subtype.val ⁻¹' A
  have hT_open : IsOpen T := hA_open.preimage continuous_subtype_val
  have hT_closed : IsClosed T := by
    rw [isClosed_induced_iff]
    refine ⟨closure A, isClosed_closure, ?_⟩
    ext x
    constructor
    · intro hx
      exact hclosure ⟨hx, x.property⟩
    · intro hx
      exact subset_closure hx
  let _ : ConnectedSpace s := Subtype.connectedSpace hs_conn
  have hT_clopen : IsClopen T := ⟨hT_closed, hT_open⟩
  have hT_univ : T = Set.univ := hT_clopen.eq_univ ⟨⟨x₀, hx₀⟩, hx₀A⟩
  intro x hx
  have hxT : (⟨x, hx⟩ : s) ∈ T := by rw [hT_univ]; exact Set.mem_univ _
  obtain ⟨o, ho, hxo, heq⟩ := hxT
  exact heq hxo

theorem hartogsext_exists_zero_germ
    {n : ℕ} (hn : 2 ≤ n)
    {U K : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U)
    {φ u : EuclideanSpace ℂ (Fin n) → ℂ}
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U)
    (hKφ : K ⊆ tsupport φ) (hφne : (tsupport φ).Nonempty)
    (huc : HasCompactSupport u)
    (hu : DifferentiableOn ℂ u (tsupport φ)ᶜ) :
    ∃ y ∈ U \ K, Filter.EventuallyEq (nhds y) u (fun _ ↦ 0) ∧
      Filter.EventuallyEq (nhds y) φ (fun _ ↦ 0) := by
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hb : Bornology.IsBounded (tsupport φ ∪ tsupport u) :=
    hφc.isCompact.isBounded.union huc.isCompact.isBounded
  have hproper : tsupport φ ∪ tsupport u ≠ Set.univ := by
    intro heq
    apply NormedSpace.unbounded_univ ℝ (EuclideanSpace ℂ (Fin n))
    rwa [← heq]
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  have haφ : a ∉ tsupport φ := fun h ↦ ha (Or.inl h)
  have hau : a ∉ tsupport u := fun h ↦ ha (Or.inr h)
  obtain ⟨p, hpφ, hpdist⟩ :=
    hφc.isCompact.exists_infDist_eq_dist hφne a
  let d := dist a p
  have hd : 0 < d := by
    have hinf : 0 < Metric.infDist a (tsupport φ) :=
      ((isClosed_tsupport φ).notMem_iff_infDist_pos hφne).mp haφ
    rw [hpdist] at hinf
    exact hinf
  have hballφ : Metric.ball a d ⊆ (tsupport φ)ᶜ := by
    intro z hz
    rw [mem_compl_iff]
    intro hzφ
    have hle : dist a p ≤ dist a z := by
      rw [← hpdist]
      exact Metric.infDist_le_dist_of_mem hzφ
    have hlt : dist a z < dist a p := by
      simpa only [d, dist_comm] using Metric.mem_ball.mp hz
    exact (not_lt_of_ge hle) hlt
  have hzero_event : Filter.EventuallyEq (nhds a) u (fun _ ↦ 0) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hau] with z hz
    exact image_eq_zero_of_notMem_tsupport hz
  have hzero_ball : Set.EqOn u
      (fun _ : EuclideanSpace ℂ (Fin n) ↦ (0 : ℂ)) (Metric.ball a d) := by
    apply hartogsext_eqOn_of_differentiableOn_of_isConnected
      Metric.isOpen_ball
      ⟨⟨a, Metric.mem_ball_self hd⟩, (convex_ball a d).isPreconnected⟩
      (hu.mono hballφ) (differentiable_const (c := (0 : ℂ))).differentiableOn
      (Metric.mem_ball_self hd) hzero_event
  have hpclosed : p ∈ Metric.closedBall a d := by
    rw [Metric.mem_closedBall]
    simp only [d, dist_comm, le_refl]
  have hpclosure : p ∈ closure (Metric.ball a d) := by
    rw [closure_ball a hd.ne']
    exact hpclosed
  obtain ⟨y, hyU, hyball⟩ := mem_closure_iff_nhds.mp hpclosure U
    (hU.mem_nhds (hφU hpφ))
  have hyφ : y ∉ tsupport φ := by
    exact hballφ hyball
  refine ⟨y, ⟨hyU, fun hyK ↦ hyφ (hKφ hyK)⟩, ?_, ?_⟩
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyball] with z hz
    exact hzero_ball hz
  · filter_upwards [Metric.isOpen_ball.mem_nhds hyball] with z hz
    exact image_eq_zero_of_notMem_tsupport
      (hballφ hz)

/--
Let `U ⊆ ℂⁿ` be open connected with `2 ≤ n`, `K ⊆ U` compact with `U \ K` connected. Every `f : ℂⁿ
→ ℂ` holomorphic on `U \ K` extends to holomorphic `F` on `U` with `Set.EqOn F f (U \ K)`. Here
`ℂⁿ` is `EuclideanSpace ℂ (Fin n)`. Source: Hartogs extension phenomenon, F. Hartogs, Math. Ann.
62 (1906); see Hörmander, An Introduction to Complex Analysis in Several Variables; Lean is ℂⁿ n ≥
2 finite-dimensional form via EuclideanSpace ℂ (Fin n) with U open connected K compact U\K
connected.

Proves `Wanted` entry `hartogs_extension`.

Proof: The compactly supported Cauchy–Green equation in one coordinate, combined with a smooth
cutoff and one-variable identity continuation.
-/
theorem hartogs_extension
    {n : ℕ} (hn : 2 ≤ n)
    {U : Set (EuclideanSpace ℂ (Fin n))} (hU_open : IsOpen U) (_hU_conn : IsConnected U)
    {K : Set (EuclideanSpace ℂ (Fin n))} (hK_compact : IsCompact K) (hKU : K ⊆ U)
    (hUK_conn : IsConnected (U \ K))
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f (U \ K)) :
    ∃ F : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ F U ∧ Set.EqOn F f (U \ K) := by
  by_cases hKne : K.Nonempty
  · let W := U \ K
    have hW_open : IsOpen W := hU_open.sdiff hK_compact.isClosed
    let i₀ : Fin n := ⟨0, lt_of_lt_of_le zero_lt_two hn⟩
    obtain ⟨χ, hχdiff, hχcompact, hχU, V, hV_open, hKV, hχone⟩ :=
      hartogsext_exists_cutoff hU_open hK_compact hKU
    let φ : EuclideanSpace ℂ (Fin n) → ℂ := Complex.ofRealCLM ∘ χ
    have hφdiff : ContDiff ℝ 2 φ := by
      exact Complex.ofRealCLM.contDiff.comp hχdiff
    have hφcompact : HasCompactSupport φ := by
      exact hχcompact.comp_left rfl
    have hφU : tsupport φ ⊆ U := by
      exact (tsupport_comp_subset rfl χ).trans hχU
    have hφone : Set.EqOn φ (fun _ ↦ 1) V := by
      intro x hx
      simp only [φ, Function.comp_apply, Complex.ofRealCLM_apply]
      rw [hχone hx]
      exact Complex.ofReal_one
    have hKφ : K ⊆ tsupport φ := by
      intro x hx
      apply subset_tsupport φ
      rw [Function.mem_support, hφone (hKV hx)]
      norm_num
    have hφne : (tsupport φ).Nonempty := hKne.mono hKφ
    let a : Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
      fun j ↦ hartogsextBarPartial j φ
    have ha_diff (j : Fin n) : ContDiff ℝ 1 (a j) := by
      exact hartogsext_contDiff_barPartial hφdiff j
    have ha_compact (j : Fin n) : HasCompactSupport (a j) := by
      exact hartogsext_hasCompactSupport_barPartial hφcompact j
    have haW (j : Fin n) : tsupport (a j) ⊆ W := by
      intro x hx
      refine ⟨hφU (hartogsext_tsupport_barPartial_subset j hx), ?_⟩
      intro hxK
      have hxcompl := hartogsext_tsupport_barPartial_subset_compl
        hV_open hφone j hx
      exact hxcompl (hKV hxK)
    have hf_real : ContDiffOn ℝ 1 f W :=
      hartogsext_differentiableOn_contDiffOn_one_real hW_open hf
    let g : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ f x * a i₀ x
    have hg_diff : ContDiff ℝ 1 g := by
      exact hartogsext_contDiff_mul_of_tsupport_subset
        hW_open hf_real (ha_diff i₀) (haW i₀)
    have hg_compact : HasCompactSupport g := by
      exact (ha_compact i₀).mul_left
    let b : Fin n → EuclideanSpace ℂ (Fin n) → ℂ :=
      fun j x ↦ f x * a j x
    have hb_diff (j : Fin n) : ContDiff ℝ 1 (b j) := by
      exact hartogsext_contDiff_mul_of_tsupport_subset
        hW_open hf_real (ha_diff j) (haW j)
    have hb_compact (j : Fin n) : HasCompactSupport (b j) := by
      exact (ha_compact j).mul_left
    have hcompat (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
        hartogsextBarPartial j g x = hartogsextBarPartial i₀ (b j) x := by
      by_cases hxW : x ∈ W
      · have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hfR : DifferentiableAt ℝ f x := hfd.restrictScalars ℝ
        have hai (k : Fin n) : DifferentiableAt ℝ (a k) x :=
          (ha_diff k).differentiable (by norm_num) x
        rw [show hartogsextBarPartial j g x =
            hartogsextBarPartial j (fun y ↦ f y * a i₀ y) x by rfl,
          hartogsext_barPartial_mul hfR (hai i₀) j,
          show hartogsextBarPartial i₀ (b j) x =
            hartogsextBarPartial i₀ (fun y ↦ f y * a j y) x by rfl,
          hartogsext_barPartial_mul hfR (hai j) i₀,
          hartogsext_barPartial_eq_zero_of_differentiableAt hfd j,
          hartogsext_barPartial_eq_zero_of_differentiableAt hfd i₀]
        simp only [zero_mul, zero_add]
        exact congrArg (fun z : ℂ ↦ f x * z)
          (hartogsext_barPartial_comm hφdiff j i₀ x)
      · have hxg : x ∉ tsupport g := by
          intro hxg
          apply hxW
          apply haW i₀
          exact tsupport_mul_subset_right hxg
        have hxb : x ∉ tsupport (b j) := by
          intro hxb
          apply hxW
          apply haW j
          exact tsupport_mul_subset_right hxb
        rw [hartogsext_barPartial_eq_zero_of_notMem_tsupport hxg,
          hartogsext_barPartial_eq_zero_of_notMem_tsupport hxb]
    let u := hartogsextPartialCauchyGreen i₀ g
    have hu_diff : ContDiff ℝ 1 u :=
      hartogsext_contDiff_partialCauchyGreen hg_compact hg_diff i₀
    have hu_bar (j : Fin n) (x : EuclideanSpace ℂ (Fin n)) :
        hartogsextBarPartial j u x = b j x := by
      calc
        hartogsextBarPartial j u x =
            hartogsextPartialCauchyGreen i₀
              (hartogsextBarPartial j g) x :=
          hartogsext_barPartial_partialCauchyGreen
            hg_compact hg_diff i₀ j x
        _ = hartogsextPartialCauchyGreen i₀
              (hartogsextBarPartial i₀ (b j)) x := by
          rw [show hartogsextBarPartial j g =
            hartogsextBarPartial i₀ (b j) from funext (hcompat j)]
        _ = hartogsextBarPartial i₀
              (hartogsextPartialCauchyGreen i₀ (b j)) x :=
          (hartogsext_barPartial_partialCauchyGreen
            (hb_compact j) (hb_diff j) i₀ i₀ x).symm
        _ = b j x := hartogsext_barPartial_partialCauchyGreen_self
          (hb_compact j) (hb_diff j) i₀ x
    have hu_compact : HasCompactSupport u :=
      hartogsext_hasCompactSupport_partialCauchyGreen hn hg_compact hg_diff i₀
        hb_compact hu_bar
    let q : EuclideanSpace ℂ (Fin n) → ℂ :=
      fun x ↦ (1 - φ x) * f x
    have hq_event_of_mem_K {x : EuclideanSpace ℂ (Fin n)} (hxK : x ∈ K) :
        Filter.EventuallyEq (nhds x) q (fun _ ↦ 0) := by
      filter_upwards [hV_open.mem_nhds (hKV hxK)] with y hy
      simp only [q, hφone hy, sub_self, zero_mul]
    have hq_diff_at {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) :
        DifferentiableAt ℝ q x := by
      by_cases hxK : x ∈ K
      · exact (hasFDerivAt_zero_of_eventually_const
          (0 : ℂ) (hq_event_of_mem_K hxK)).differentiableAt
      · have hxW : x ∈ W := ⟨hxU, hxK⟩
        have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hφd : DifferentiableAt ℝ φ x :=
          hφdiff.differentiable (by norm_num) x
        exact ((differentiable_const (c := (1 : ℂ)) x).sub hφd).mul
          (hfd.restrictScalars ℝ)
    let F : EuclideanSpace ℂ (Fin n) → ℂ := fun x ↦ q x + u x
    have hF_real {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) :
        DifferentiableAt ℝ F x :=
      (hq_diff_at hxU).add (hu_diff.differentiable (by norm_num) x)
    have hF_bar {x : EuclideanSpace ℂ (Fin n)} (hxU : x ∈ U) (j : Fin n) :
        hartogsextBarPartial j F x = 0 := by
      have hqd := hq_diff_at hxU
      have hud : DifferentiableAt ℝ u x := hu_diff.differentiable (by norm_num) x
      rw [show hartogsextBarPartial j F x =
          hartogsextBarPartial j (fun y ↦ q y + u y) x by rfl,
        hartogsext_barPartial_add hqd hud j, hu_bar]
      by_cases hxK : x ∈ K
      · have hqbar : hartogsextBarPartial j q x = 0 := by
          rw [hartogsextBarPartial,
            (hasFDerivAt_zero_of_eventually_const
              (0 : ℂ) (hq_event_of_mem_K hxK)).fderiv]
          simp
        have hxaj : x ∉ tsupport (a j) := by
          intro hxaj
          have hxcompl := hartogsext_tsupport_barPartial_subset_compl
            hV_open hφone j hxaj
          exact hxcompl (hKV hxK)
        have haj : a j x = 0 := image_eq_zero_of_notMem_tsupport hxaj
        rw [hqbar]
        simp [b, haj]
      · have hxW : x ∈ W := ⟨hxU, hxK⟩
        have hfd := hf.differentiableAt (hW_open.mem_nhds hxW)
        have hfR : DifferentiableAt ℝ f x := hfd.restrictScalars ℝ
        have hφR : DifferentiableAt ℝ φ x :=
          hφdiff.differentiable (by norm_num) x
        let p : EuclideanSpace ℂ (Fin n) → ℂ := fun y ↦ 1 - φ y
        have hpR : DifferentiableAt ℝ p x :=
          (differentiable_const (c := (1 : ℂ)) x).sub hφR
        have hpbar : hartogsextBarPartial j p x = -a j x :=
          hartogsext_barPartial_one_sub φ x j
        have hqbar : hartogsextBarPartial j q x = (-a j x) * f x := by
          change hartogsextBarPartial j (fun y ↦ p y * f y) x = _
          rw [hartogsext_barPartial_mul hpR hfR j, hpbar,
            hartogsext_barPartial_eq_zero_of_differentiableAt hfd j]
          simp
        rw [hqbar]
        simp only [b]
        ring
    have hF_diff : DifferentiableOn ℂ F U := by
      intro x hxU
      exact (hartogsext_differentiableAt_of_barPartial_eq_zero
        (hF_real hxU) (hF_bar hxU)).differentiableWithinAt
    have hu_holo : DifferentiableOn ℂ u (tsupport φ)ᶜ := by
      intro x hx
      apply (hartogsext_differentiableAt_of_barPartial_eq_zero
        (hu_diff.differentiable (by norm_num) x) ?_).differentiableWithinAt
      intro j
      rw [hu_bar]
      have hxaj : x ∉ tsupport (a j) := by
        intro hxaj
        exact hx (hartogsext_tsupport_barPartial_subset j hxaj)
      have haj : a j x = 0 := image_eq_zero_of_notMem_tsupport hxaj
      simp [b, haj]
    obtain ⟨y, hyW, huy, hφy⟩ := hartogsext_exists_zero_germ
      hn hU_open hφcompact hφU hKφ hφne hu_compact hu_holo
    have hFf : Filter.EventuallyEq (nhds y) F f := by
      filter_upwards [huy, hφy] with x hux hφx
      simp [F, q, hux, hφx]
    have hEq : Set.EqOn F f W :=
      hartogsext_eqOn_of_differentiableOn_of_isConnected
        hW_open hUK_conn (hF_diff.mono fun x hx ↦ hx.1) hf hyW hFf
    exact ⟨F, hF_diff, hEq⟩
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    subst K
    refine ⟨f, ?_, ?_⟩
    · simpa using hf
    · intro x hx
      rfl

end Complex.HartogsWanted
