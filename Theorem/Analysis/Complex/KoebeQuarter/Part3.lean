/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.Complex.KoebeQuarter.Part2
/-!
# Koebe one-quarter theorem
-/


section

namespace Complex.KoebeQuarterWanted

open MeasureTheory

theorem koebeEll_apply (ρ : ℝ) (c ζ : ℂ) :
    koebeEll ρ c ζ = ((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ) + c * (ρ : ℂ) * ζ := by
  have hconj : Complex.conjAe.toLinearEquiv.toLinearMap ζ = (starRingEnd ℂ ζ) := rfl
  simp only [koebeEll, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.mulLeft_apply, hconj, mul_assoc]

theorem koebeEll_norm_bounds (ρ : ℝ) (c ζ : ℂ) (hρ : 0 < ρ) :
    (ρ⁻¹ - ‖c‖ * ρ) * ‖ζ‖ ≤ ‖koebeEll ρ c ζ‖ ∧
      ‖koebeEll ρ c ζ‖ ≤ (ρ⁻¹ + ‖c‖ * ρ) * ‖ζ‖ := by
  rw [koebeEll_apply]
  have hA : ‖((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ)‖ = ρ⁻¹ * ‖ζ‖ := by
    rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ)]
  have hB : ‖c * (ρ : ℂ) * ζ‖ = ‖c‖ * ρ * ‖ζ‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ.le]
  constructor
  · have h := norm_sub_norm_le (((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ))
      (-(c * (ρ : ℂ) * ζ))
    rw [norm_neg, sub_neg_eq_add] at h
    rw [hA, hB] at h
    have heq : (ρ⁻¹ - ‖c‖ * ρ) * ‖ζ‖ = ρ⁻¹ * ‖ζ‖ - ‖c‖ * ρ * ‖ζ‖ := by
      ring
    rw [heq]
    exact h
  · have h := norm_add_le (((ρ⁻¹ : ℝ) : ℂ) * (starRingEnd ℂ ζ)) (c * (ρ : ℂ) * ζ)
    rw [hA, hB] at h
    have heq : (ρ⁻¹ + ‖c‖ * ρ) * ‖ζ‖ = ρ⁻¹ * ‖ζ‖ + ‖c‖ * ρ * ‖ζ‖ := by
      ring
    rw [heq]
    exact h

theorem koebeEll_gap_pos (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) : 0 < ρ⁻¹ - ‖c‖ * ρ := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have h1 : ‖c‖ * ρ < ρ⁻¹ := by
    have h3 : ‖c‖ * ρ = (‖c‖ * ρ ^ 2) * ρ⁻¹ := by
      field_simp
    rw [h3]
    have h4 : (‖c‖ * ρ ^ 2) * ρ⁻¹ < 1 * ρ⁻¹ :=
      mul_lt_mul_of_pos_right h (inv_pos.mpr hρ)
    rwa [one_mul] at h4
  linarith

theorem koebeEll_injective (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) : Function.Injective (koebeEll ρ c) := by
  intro ζ₁ ζ₂ h12
  have hpos := koebeEll_gap_pos ρ c hρ h
  have hL : koebeEll ρ c (ζ₁ - ζ₂) = 0 := by
    rw [map_sub, h12, sub_self]
  have hnorm := (koebeEll_norm_bounds ρ c (ζ₁ - ζ₂) hρ).1
  rw [hL, norm_zero] at hnorm
  have h0 : ‖ζ₁ - ζ₂‖ = 0 := by
    rcases eq_or_lt_of_le (norm_nonneg (ζ₁ - ζ₂)) with hcon | hcon
    · exact hcon.symm
    · have hmul := mul_pos hpos hcon
      linarith
  have hsub : ζ₁ - ζ₂ = 0 := norm_eq_zero.mp h0
  exact sub_eq_zero.mp hsub

theorem koebeEll_preimage (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) (t : ℝ) (e : ℂ)
    (he : ‖e‖ ≤ t * (ρ⁻¹ - ‖c‖ * ρ)) :
    ∃ η : ℂ, ‖η‖ ≤ t ∧ koebeEll ρ c η = e := by
  have hpos := koebeEll_gap_pos ρ c hρ h
  obtain ⟨η, hη⟩ := LinearMap.injective_iff_surjective.mp
    (koebeEll_injective ρ c hρ h) e
  refine ⟨η, ?_, hη⟩
  have h1 : (ρ⁻¹ - ‖c‖ * ρ) * ‖η‖ ≤ ‖e‖ := by
    rw [← hη]
    exact (koebeEll_norm_bounds ρ c η hρ).1
  have h2 : t * (ρ⁻¹ - ‖c‖ * ρ) = (ρ⁻¹ - ‖c‖ * ρ) * t := by ring
  rw [h2] at he
  have hle : (ρ⁻¹ - ‖c‖ * ρ) * ‖η‖ ≤ (ρ⁻¹ - ‖c‖ * ρ) * t :=
    le_trans h1 he
  exact le_of_mul_le_mul_left hle hpos

theorem koebeEll_toMatrix (ρ : ℝ) (c : ℂ) :
    LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (koebeEll ρ c) =
      !![ρ⁻¹ + c.re * ρ, -(c.im * ρ); c.im * ρ, c.re * ρ - ρ⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr,
      Complex.coe_basisOneI, koebeEll_apply, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem koebeEll_det (ρ : ℝ) (c : ℂ) :
    LinearMap.det (koebeEll ρ c) = ‖c‖ ^ 2 * ρ ^ 2 - ρ⁻¹ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, koebeEll_toMatrix,
    Matrix.det_fin_two_of]
  have hsq : ‖c‖ ^ 2 = c.re * c.re + c.im * c.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  rw [hsq]
  ring

theorem koebeEll_det_abs (ρ : ℝ) (c : ℂ) (hρ : 0 < ρ)
    (h : ‖c‖ * ρ ^ 2 < 1) :
    |LinearMap.det (koebeEll ρ c)| = ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
  have hnn0 : 0 ≤ ‖c‖ * ρ ^ 2 := by positivity
  have hsq1 : (‖c‖ * ρ ^ 2) ^ 2 < 1 := by
    have hlt := pow_lt_pow_left₀ h hnn0 two_ne_zero
    rwa [one_pow] at hlt
  have hnn : ‖c‖ ^ 2 * ρ ^ 2 ≤ ρ⁻¹ ^ 2 := by
    have hρne : ρ ≠ 0 := ne_of_gt hρ
    have h2 : ‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2 < 1 := by
      have heq : ‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2 = (‖c‖ * ρ ^ 2) ^ 2 := by ring
      rw [heq]
      exact hsq1
    have h3 : ‖c‖ ^ 2 * ρ ^ 2 = (‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2) * ρ⁻¹ ^ 2 := by
      field_simp
    rw [h3]
    have hpos : (0 : ℝ) < ρ⁻¹ ^ 2 := pow_pos (inv_pos.mpr hρ) 2
    have h4 : (‖c‖ ^ 2 * ρ ^ 2 * ρ ^ 2) * ρ⁻¹ ^ 2 < 1 * ρ⁻¹ ^ 2 :=
      mul_lt_mul_of_pos_right h2 hpos
    rw [one_mul] at h4
    exact le_of_lt h4
  rw [koebeEll_det, abs_of_nonpos (by linarith)]
  ring

theorem koebeEll_volume (ρ : ℝ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hρ : 0 < ρ) (h : ‖c‖ * ρ ^ 2 < 1) :
    volume (koebeEll ρ c '' Metric.closedBall 0 R) =
      ENNReal.ofReal (Real.pi * R ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
  have hdet := koebeEll_det_abs ρ c hρ h
  have hD : 0 ≤ ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
    rw [← hdet]
    exact abs_nonneg _
  have hpi : (NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hreal : Real.pi * R ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
      = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) * (R ^ 2 * Real.pi) := by ring
  have hR2 : ENNReal.ofReal R ^ 2 = ENNReal.ofReal (R ^ 2) := by
    rw [ENNReal.ofReal_pow hR]
  rw [MeasureTheory.Measure.addHaar_image_linearMap volume _ _,
    Complex.volume_closedBall, hdet, hpi, hR2, hreal,
    ENNReal.ofReal_mul hD, ENNReal.ofReal_mul (sq_nonneg R)]

theorem koebe_dslope_bound (k : ℂ → ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1)) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M := by
  have hnhds : Metric.ball (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
    Metric.ball_mem_nhds 0 (by norm_num)
  have hk1 : DifferentiableOn ℂ (dslope k 0) (Metric.ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope hnhds).mpr hk
  have hsub : Metric.closedBall (0 : ℂ) (1 / 4 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hcont : ContinuousOn (dslope k 0) (Metric.closedBall (0 : ℂ) (1 / 4)) :=
    (hk1.mono hsub).continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_closedBall _ _) hcont
  exact ⟨max C 1, le_max_right _ _,
    fun w hw => le_trans (hC w hw) (le_max_left _ _)⟩

theorem koebe_G_circle_mem (k G : ℂ → ℂ) (c : ℂ) (ρ M : ℝ) (ζ : ℂ)
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2)
    (hζ : ‖ζ‖ = 1) :
    G ((ρ : ℂ) * ζ) ∈
      koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
  have hρne : ρ ≠ 0 := ne_of_gt hρ0
  have hζne : ζ ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hζ
    norm_num at hζ
  have hmul : ζ * starRingEnd ℂ ζ = 1 := by
    have hmc := Complex.mul_conj' ζ
    rw [hζ] at hmc
    simpa using hmc
  have hconj : ζ⁻¹ = starRingEnd ℂ ζ := by
    calc ζ⁻¹ = ζ⁻¹ * 1 := by rw [mul_one]
      _ = ζ⁻¹ * (ζ * starRingEnd ℂ ζ) := by rw [hmul]
      _ = starRingEnd ℂ ζ := by
        rw [← mul_assoc, inv_mul_cancel₀ hζne, one_mul]
  have hinv : (((ρ : ℝ) : ℂ) * ζ)⁻¹
      = ((ρ⁻¹ : ℝ) : ℂ) * starRingEnd ℂ ζ := by
    rw [mul_inv, hconj, ← Complex.ofReal_inv]
  have hkk : k ((((ρ : ℝ) : ℂ) * ζ) ^ 2)
      = c + (((ρ : ℝ) : ℂ) * ζ) ^ 2 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2) := by
    have hds := sub_smul_dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)
    rw [smul_eq_mul, sub_zero, ← hc] at hds
    linear_combination -hds
  have hGexp : G (((ρ : ℝ) : ℂ) * ζ)
      = koebeEll ρ c ζ
        + (((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2) := by
    rw [hG, hinv, hkk, koebeEll_apply]
    ring
  have hn2 : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 2‖ = ρ ^ 2 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0.le, hζ]
    ring
  have hmem : (((ρ : ℝ) : ℂ) * ζ) ^ 2 ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
    rw [Metric.mem_closedBall, dist_zero_right, hn2]
    have hle := pow_le_pow_left₀ hρ0.le hρ2 2
    norm_num at hle ⊢
    exact hle
  have hn3 : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 3‖ = ρ ^ 3 := by
    rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hρ0.le, hζ]
    ring
  have herr : ‖(((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)‖
      ≤ M * ρ ^ 3 := by
    rw [norm_mul, hn3, mul_comm M (ρ ^ 3)]
    exact mul_le_mul_of_nonneg_left (hk1 _ hmem) (pow_nonneg hρ0.le 3)
  have hlt : ‖c‖ * ρ ^ 2 < 1 := lt_of_le_of_lt hρc (by norm_num)
  have hpos := koebeEll_gap_pos ρ c hρ0 hlt
  have hd : ρ * (ρ⁻¹ - ‖c‖ * ρ) = 1 - ‖c‖ * ρ ^ 2 := by
    rw [mul_sub, mul_inv_cancel₀ hρne]
    ring
  have key : M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ) ≤ 4 * M * ρ ^ 4 := by
    rw [div_le_iff₀ hpos]
    have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
    have hnn3 : (0 : ℝ) ≤ M * ρ ^ 3 :=
      mul_nonneg hM0 (pow_nonneg hρ0.le 3)
    have h4 : (1 : ℝ) ≤ 4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ)) := by
      rw [hd]
      linarith
    have h5 : M * ρ ^ 3 * 1 ≤ M * ρ ^ 3 * (4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ))) :=
      mul_le_mul_of_nonneg_left h4 hnn3
    have h6 : M * ρ ^ 3 * (4 * (ρ * (ρ⁻¹ - ‖c‖ * ρ)))
        = (4 * M * ρ ^ 4) * (ρ⁻¹ - ‖c‖ * ρ) := by ring
    rw [mul_one] at h5
    rw [h6] at h5
    exact h5
  obtain ⟨η, hηn, hηe⟩ := koebeEll_preimage ρ c hρ0 hlt
    (M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ))
    ((((ρ : ℝ) : ℂ) * ζ) ^ 3 * dslope k 0 ((((ρ : ℝ) : ℂ) * ζ) ^ 2)) (by
    have hdne : ρ⁻¹ - ‖c‖ * ρ ≠ 0 := ne_of_gt hpos
    have heq : M * ρ ^ 3 / (ρ⁻¹ - ‖c‖ * ρ) * (ρ⁻¹ - ‖c‖ * ρ) = M * ρ ^ 3 :=
      div_mul_cancel₀ _ hdne
    rw [heq]
    exact herr)
  refine ⟨ζ + η, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right]
    have htri := norm_add_le ζ η
    linarith [htri, hζ, hηn, key]
  · rw [map_add, hηe, hGexp]

theorem koebe_compl_subset_image (k G : ℂ → ℂ) (c : ℂ) (ρ M : ℝ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → DifferentiableAt ℂ G z)
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2) :
    (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ⊆
      G '' (Metric.ball 0 ρ \ {0}) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
  have hlt : ‖c‖ * ρ ^ 2 < 1 := lt_of_le_of_lt hρc (by norm_num)
  have hpos := koebeEll_gap_pos ρ c hρ0 hlt
  have hbij : Function.Bijective (koebeEll ρ c) :=
    ⟨koebeEll_injective ρ c hρ0 hlt,
      LinearMap.injective_iff_surjective.mp
        (koebeEll_injective ρ c hρ0 hlt)⟩
  set K := (ρ⁻¹ + ‖c‖ * ρ) * (1 + 4 * M * ρ ^ 4) with hKdef
  have hK0 : (0 : ℝ) ≤ K := by
    rw [hKdef]
    apply mul_nonneg
    · have h1 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
      have h2 : (0 : ℝ) ≤ ‖c‖ * ρ := mul_nonneg (norm_nonneg _) hρ0.le
      linarith
    · have h3 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
        mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
      linarith
  have hPcont : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    have heq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2)
        = (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) *
          Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I)) := by
      funext p
      exact circleMap_zero p.1 p.2
    rw [heq]
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp continuous_fst
    · apply Complex.continuous_exp.comp
      apply Continuous.mul _ continuous_const
      exact Complex.continuous_ofReal.comp continuous_snd
  have hUopen : IsOpen (Metric.ball (0 : ℂ) ρ \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have hUball : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by linarith)
  have hUsub : Metric.ball (0 : ℂ) ρ \ {0} ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
    intro z hz
    exact ⟨hUball hz.1, hz.2⟩
  have hUeq : (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) ''
      (Set.Ioo 0 ρ ×ˢ Set.univ) = Metric.ball 0 ρ \ {0} := by
    ext w
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      have ht0 : 0 < t := ht.1
      have htρ : t < ρ := ht.2
      have hn : ‖circleMap 0 t θ‖ = t := by
        rw [norm_circleMap_zero, abs_of_pos ht0]
      constructor
      · rw [Metric.mem_ball, dist_zero_right, hn]
        exact htρ
      · rw [Set.mem_singleton_iff]
        intro hcon
        have hcon' : circleMap 0 t θ = 0 := hcon
        rw [hcon', norm_zero] at hn
        linarith
    · rintro ⟨hwball, hwne⟩
      have hw0 : w ≠ 0 := fun h => hwne (Set.mem_singleton_iff.mpr h)
      have ht0 : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have htρ : ‖w‖ < ρ := by
        have h := Metric.mem_ball.mp hwball
        rwa [dist_zero_right] at h
      refine ⟨(‖w‖, Complex.arg w), ⟨⟨ht0, htρ⟩, Set.mem_univ _⟩, ?_⟩
      have harg := Complex.norm_mul_exp_arg_mul_I w
      simp only []
      rw [circleMap_zero]
      exact harg
  have hUconn : IsPreconnected (Metric.ball (0 : ℂ) ρ \ {0}) := by
    rw [← hUeq]
    exact IsPreconnected.image (isPreconnected_Ioo.prod isPreconnected_univ)
      (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) hPcont.continuousOn
  have hRnn : (0 : ℝ) ≤ 1 + 4 * M * ρ ^ 4 := by
    have h1 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    linarith
  have hSeq : (fun p : ℝ × ℝ => koebeEll ρ c (circleMap 0 p.1 p.2)) ''
      (Set.Ioi (1 + 4 * M * ρ ^ 4) ×ˢ Set.univ)
      = (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := by
    ext w
    constructor
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      intro hcon
      obtain ⟨x, hxmem, heq⟩ := hcon
      have xinj : x = circleMap 0 t θ := hbij.1 heq
      have hxle : ‖x‖ ≤ 1 + 4 * M * ρ ^ 4 := by
        have h := Metric.mem_closedBall.mp hxmem
        rwa [dist_zero_right] at h
      rw [xinj, norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt hRnn ht)] at hxle
      exact absurd hxle (not_le.mpr ht)
    · intro hw
      obtain ⟨x, hx⟩ := hbij.2 w
      have hxnb : x ∉ Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
        intro hmem
        exact hw ⟨x, hmem, hx⟩
      have hxR : 1 + 4 * M * ρ ^ 4 < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hxnb
        exact hxnb
      refine ⟨(‖x‖, Complex.arg x), ⟨hxR, Set.mem_univ _⟩, ?_⟩
      have harg := Complex.norm_mul_exp_arg_mul_I x
      simp only []
      rw [circleMap_zero]
      rw [harg, hx]
  have hSconn : IsPreconnected
      (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := by
    rw [← hSeq]
    have hLcont : Continuous (koebeEll ρ c) := by
      have heq : koebeEll ρ c
          = (fun ζ : ℂ => ((ρ⁻¹ : ℝ) : ℂ) * starRingEnd ℂ ζ +
            c * (ρ : ℂ) * ζ) := by
        funext ζ
        exact koebeEll_apply ρ c ζ
      rw [heq]
      apply Continuous.add
      · apply Continuous.mul continuous_const
        exact Complex.continuous_conj
      · apply Continuous.mul continuous_const continuous_id
    exact IsPreconnected.image (isPreconnected_Ioi.prod isPreconnected_univ)
      (fun p : ℝ × ℝ => koebeEll ρ c (circleMap 0 p.1 p.2))
      (hLcont.comp hPcont).continuousOn
  obtain ⟨N, hN⟩ : ∃ N : ℝ,
      ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖k w‖ ≤ N := by
    have hsub : Metric.closedBall (0 : ℂ) (1 / 4 : ℝ) ⊆ Metric.ball (0 : ℂ) 1 := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right] at hz
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    exact IsCompact.exists_bound_of_continuousOn (isCompact_closedBall _ _)
      ((hk.mono hsub).continuousOn)
  set N₁ := |N| + 1 with hN₁def
  have hN0 : (0 : ℝ) ≤ N₁ := by
    rw [hN₁def]
    positivity
  have hNk : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖k w‖ ≤ N₁ := by
    intro w hw
    have h1 := hN w hw
    rw [hN₁def]
    linarith [le_abs_self N]
  have hGlower : ∀ z ∈ Metric.ball (0 : ℂ) ρ, z ≠ 0 →
      ‖z‖⁻¹ - ‖z‖ * N₁ ≤ ‖G z‖ := by
    intro z hz hzne
    have hzn : ‖z‖ < ρ := by
      have h := Metric.mem_ball.mp hz
      rwa [dist_zero_right] at h
    have hz2mem : z ^ 2 ∈ Metric.closedBall (0 : ℂ) (1 / 4) := by
      rw [Metric.mem_closedBall, dist_zero_right, norm_pow]
      have h1 : ‖z‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn.le 2
      have h2 : ρ ^ 2 ≤ 1 / 4 := by
        have hle := pow_le_pow_left₀ hρ0.le hρ2 2
        norm_num at hle ⊢
        exact hle
      linarith
    have hkN : ‖k (z ^ 2)‖ ≤ N₁ := hNk _ hz2mem
    rw [hG z]
    have hA : ‖z⁻¹‖ = ‖z‖⁻¹ := norm_inv z
    have hB : ‖z * k (z ^ 2)‖ = ‖z‖ * ‖k (z ^ 2)‖ := norm_mul _ _
    have h := norm_sub_norm_le z⁻¹ (-(z * k (z ^ 2)))
    rw [norm_neg, sub_neg_eq_add] at h
    rw [hA, hB] at h
    have hle : ‖z‖ * ‖k (z ^ 2)‖ ≤ ‖z‖ * N₁ :=
      mul_le_mul_of_nonneg_left hkN (norm_nonneg _)
    linarith
  have hGdiffU : DifferentiableOn ℂ G (Metric.ball 0 ρ \ {0}) := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0 : ℂ) 1 := hUball hz.1
    have hzne : z ≠ 0 := fun hcon => hz.2 (Set.mem_singleton_iff.mpr hcon)
    exact ((hGdiff z hz1 hzne).differentiableWithinAt).mono
      (Set.sdiff_subset.trans hUball)
  have hGanalytic : AnalyticOnNhd ℂ G (Metric.ball 0 ρ \ {0}) :=
    hGdiffU.analyticOnNhd hUopen
  have hmemU : ∀ s : ℝ, 0 < s → s < ρ → ((s : ℝ) : ℂ) ∈
      Metric.ball 0 ρ \ {0} := by
    intro s hs0 hsρ
    constructor
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      exact hsρ
    · rw [Set.mem_singleton_iff]
      intro hcon
      have h2 : (s : ℝ) = 0 := by exact_mod_cast hcon
      linarith
  have hGnonconst : ¬ ∃ w, ∀ z ∈ Metric.ball 0 ρ \ {0}, G z = w := by
    rintro ⟨w, hw⟩
    have ha := hmemU (ρ / 2) (by linarith) (by linarith)
    have hb := hmemU (ρ / 4) (by linarith) (by linarith)
    have e1 := hw _ ha
    have e2 := hw _ hb
    have einj := hGinj (hUsub ha) (hUsub hb) (by rw [e1, e2])
    have hconr : (ρ / 2 : ℝ) = ρ / 4 := by exact_mod_cast einj
    linarith
  have hVopen : IsOpen (G '' (Metric.ball 0 ρ \ {0})) := by
    have hor := hGanalytic.is_constant_or_isOpen hUconn
    rcases hor with hconst | hopen
    · exact absurd hconst hGnonconst
    · exact hopen _ (fun x hx => hx) hUopen
  have hInter : ((koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ∩
      G '' (Metric.ball 0 ρ \ {0})).Nonempty := by
    set t := min (ρ / 2) (min (1 / (2 * (K + 1))) (1 / (2 * (N₁ + 1))))
      with htdef
    have ht0 : 0 < t := by
      rw [htdef]
      apply lt_min (by linarith)
      apply lt_min
      · apply div_pos (by norm_num)
        have hlt1 : (0 : ℝ) < K + 1 := by linarith
        linarith
      · apply div_pos (by norm_num)
        have hlt1 : (0 : ℝ) < N₁ + 1 := by linarith
        linarith
    have htρ : t < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htK : t * (2 * (K + 1)) ≤ 1 := by
      have h1 : t ≤ 1 / (2 * (K + 1)) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have hpos2 : (0 : ℝ) < 2 * (K + 1) := by
        have hlt1 : (0 : ℝ) < K + 1 := by linarith
        linarith
      rw [le_div_iff₀ hpos2] at h1
      exact h1
    have htN : t * (2 * (N₁ + 1)) ≤ 1 := by
      have h1 : t ≤ 1 / (2 * (N₁ + 1)) :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      have hpos2 : (0 : ℝ) < 2 * (N₁ + 1) := by
        have hlt1 : (0 : ℝ) < N₁ + 1 := by linarith
        linarith
      rw [le_div_iff₀ hpos2] at h1
      exact h1
    have htinv : 2 * (K + 1) ≤ t⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ ht0]
      linarith [htK]
    have htN' : t * N₁ ≤ 1 / 2 := by
      have h1 : t * (2 * N₁) ≤ t * (2 * (N₁ + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) ht0.le
      linarith [htN]
    have htm := hmemU t ht0 htρ
    refine ⟨G ((t : ℝ) : ℂ), ?_, ⟨_, htm, rfl⟩⟩
    rw [Set.mem_compl_iff]
    rintro ⟨η, hηmem, hηe⟩
    have hηn : ‖η‖ ≤ 1 + 4 * M * ρ ^ 4 := by
      have h := Metric.mem_closedBall.mp hηmem
      rwa [dist_zero_right] at h
    have hKbound : ‖koebeEll ρ c η‖ ≤ K := by
      rw [hKdef]
      have hb := (koebeEll_norm_bounds ρ c η hρ0).2
      have hle : (ρ⁻¹ + ‖c‖ * ρ) * ‖η‖
          ≤ (ρ⁻¹ + ‖c‖ * ρ) * (1 + 4 * M * ρ ^ 4) := by
        apply mul_le_mul_of_nonneg_left hηn
        have h1 : (0 : ℝ) < ρ⁻¹ := inv_pos.mpr hρ0
        have h2 : (0 : ℝ) ≤ ‖c‖ * ρ := mul_nonneg (norm_nonneg _) hρ0.le
        linarith
      linarith
    have hGlb := hGlower _ htm.1
      (fun hcon => htm.2 (Set.mem_singleton_iff.mpr hcon))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0] at hGlb
    rw [← hηe] at hGlb
    linarith [hGlb, hKbound, htinv, htN']
  have hClosure : closure (G '' (Metric.ball 0 ρ \ {0})) ∩
      (koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ ⊆
      G '' (Metric.ball 0 ρ \ {0}) := by
    intro w ⟨hwcl, hwS⟩
    obtain ⟨z, hzm, hzt⟩ := mem_closure_iff_seq_limit.mp hwcl
    have hzm' : ∀ n, ∃ y, y ∈ Metric.ball 0 ρ \ {0} ∧ G y = z n := hzm
    choose y hymem hyG using hzm'
    have hymem' : ∀ n, y n ∈ Metric.closedBall (0 : ℂ) ρ := by
      intro n
      exact Metric.ball_subset_closedBall (hymem n).1
    obtain ⟨zstar, hzstar, φ, hφmono, hφlim⟩ :=
      IsCompact.tendsto_subseq (isCompact_closedBall _ _) hymem'
    have hGlim : Filter.Tendsto (fun n => G (y (φ n))) Filter.atTop (nhds w) :=
      (hzt.comp hφmono.tendsto_atTop).congr (fun n => (hyG (φ n)).symm)
    have hzne : zstar ≠ 0 := by
      intro hcon
      have hylim0 : Filter.Tendsto (fun n => ‖y (φ n)‖) Filter.atTop (nhds 0) := by
        have h0 : Filter.Tendsto (fun n => y (φ n)) Filter.atTop (nhds 0) := by
          rw [hcon] at hφlim
          exact hφlim
        have h1 := h0.norm
        rwa [norm_zero] at h1
      have hS : (0 : ℝ) < ‖w‖ + 2 + N₁ := by linarith [norm_nonneg w, hN0]
      have hδ : (0 : ℝ) < 1 / (‖w‖ + 2 + N₁) := div_pos (by norm_num) hS
      have ev1 : ∀ᶠ n in Filter.atTop, ‖y (φ n)‖ < 1 / (‖w‖ + 2 + N₁) :=
        hylim0.eventually (Iio_mem_nhds hδ)
      have ev2 : ∀ᶠ n in Filter.atTop, ‖G (y (φ n))‖ < ‖w‖ + 1 := by
        have h1 := hGlim.norm
        have hlt1 : ‖w‖ < ‖w‖ + 1 := by linarith
        exact h1.eventually (Iio_mem_nhds hlt1)
      obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
      have hnpos : 0 < ‖y (φ n)‖ := norm_pos_iff.mpr
        (fun h => (hymem (φ n)).2 (Set.mem_singleton_iff.mpr h))
      have hlow := hGlower _ (hymem (φ n)).1
        (fun h => (hymem (φ n)).2 (Set.mem_singleton_iff.mpr h))
      have h1 : ‖w‖ + 2 + N₁ ≤ ‖y (φ n)‖⁻¹ := by
        have hlt := (inv_lt_inv₀ (div_pos (by norm_num) hS) hnpos).mpr hn1
        have hδinv : (1 / (‖w‖ + 2 + N₁))⁻¹ = ‖w‖ + 2 + N₁ := by
          rw [one_div, inv_inv]
        rw [hδinv] at hlt
        exact le_of_lt hlt
      have h2 : ‖y (φ n)‖ * N₁ ≤ 1 := by
        have h3 : ‖y (φ n)‖ * N₁ ≤ (1 / (‖w‖ + 2 + N₁)) * N₁ :=
          mul_le_mul_of_nonneg_right (le_of_lt hn1) hN0
        have h4 : (1 / (‖w‖ + 2 + N₁)) * N₁ ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one hS]
          linarith [norm_nonneg w]
        linarith
      linarith
    have hzstar1 : zstar ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]
      have h := Metric.mem_closedBall.mp hzstar
      rw [dist_zero_right] at h
      linarith
    have hGcont : ContinuousAt G zstar := (hGdiff zstar hzstar1 hzne).continuousAt
    have hwG : G zstar = w := by
      have h1 : Filter.Tendsto (fun n => G (y (φ n))) Filter.atTop (nhds (G zstar)) :=
        hGcont.tendsto.comp hφlim
      exact tendsto_nhds_unique h1 hGlim
    have hzρ : ‖zstar‖ ≤ ρ := by
      have h := Metric.mem_closedBall.mp hzstar
      rwa [dist_zero_right] at h
    rcases lt_or_ge ‖zstar‖ ρ with hltρ | hleρ
    · refine ⟨zstar, ⟨?_, ?_⟩, hwG⟩
      · rw [Metric.mem_ball, dist_zero_right]
        exact hltρ
      · intro hcon
        exact hzne (Set.mem_singleton_iff.mp hcon)
    · have heq : ‖zstar‖ = ρ := le_antisymm hzρ hleρ
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      have hρc0 : ((ρ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρne
      have hζ1 : ‖zstar / (ρ : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0,
          heq, div_self hρne]
      have hmem := koebe_G_circle_mem k G c ρ M (zstar / (ρ : ℂ)) hG hc hM
        hk1 hρ0 hρ2 hρc hζ1
      have hrew : (ρ : ℂ) * (zstar / (ρ : ℂ)) = zstar := by
        rw [mul_comm, div_mul_cancel₀ _ hρc0]
      rw [hrew] at hmem
      rw [← hwG] at hwS
      exact (hwS hmem).elim
  exact hSconn.subset_of_closure_inter_subset hVopen hInter hClosure

theorem koebe_volume_upper (k G : ℂ → ℂ) (c : ℂ) (ρ r M : ℝ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → DifferentiableAt ℂ G z)
    (hc : c = k 0)
    (hM : 1 ≤ M)
    (hk1 : ∀ w ∈ Metric.closedBall (0 : ℂ) (1 / 4), ‖dslope k 0 w‖ ≤ M)
    (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2)
    (hρr : ρ < r) (hr1 : r < 1) :
    volume (G '' koebeAnnulus ρ r) ≤
      ENNReal.ofReal (Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
        (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
  have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
  have hC := koebe_compl_subset_image k G c ρ M hk hG hGinj hGdiff hc hM hk1
    hρ0 hρ2 hρc
  have hsub01 : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.ball_subset_ball (by linarith)
  have hdisj : Disjoint (G '' koebeAnnulus ρ r)
      (G '' (Metric.ball 0 ρ \ {0})) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hxmem, rfl⟩ ⟨x', hx'mem, heq⟩
    have hxx : ρ < ‖x‖ ∧ ‖x‖ < r := hxmem
    have hx10 : x ≠ 0 := by
      intro hcon
      rw [hcon, norm_zero] at hxx
      linarith
    have hx1 : x ∈ Metric.ball (0 : ℂ) 1 \ {0} := by
      constructor
      · rw [Metric.mem_ball, dist_zero_right]
        linarith [hxx.2, hr1]
      · exact fun h => hx10 (Set.mem_singleton_iff.mp h)
    have hx2 : x' ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
      ⟨hsub01 hx'mem.1, hx'mem.2⟩
    have heqx : x' = x := hGinj hx2 hx1 heq
    have hx'ρ : ‖x'‖ < ρ := by
      have h := Metric.mem_ball.mp hx'mem.1
      rwa [dist_zero_right] at h
    rw [heqx] at hx'ρ
    linarith [hxx.1]
  have hsub : G '' koebeAnnulus ρ r ⊆
      koebeEll ρ c '' Metric.closedBall 0 (1 + 4 * M * ρ ^ 4) := by
    intro y hy
    have hyV : y ∉ G '' (Metric.ball 0 ρ \ {0}) := by
      intro hyV
      rw [Set.disjoint_left] at hdisj
      exact hdisj hy hyV
    by_contra hyS
    have hySc : y ∈ (koebeEll ρ c ''
        Metric.closedBall 0 (1 + 4 * M * ρ ^ 4))ᶜ := hyS
    exact hyV (hC hySc)
  have hRnn : (0 : ℝ) ≤ 1 + 4 * M * ρ ^ 4 := by
    have h1 : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    linarith
  have hvol := koebeEll_volume ρ c (1 + 4 * M * ρ ^ 4) hRnn hρ0
    (lt_of_le_of_lt hρc (by norm_num))
  rw [← hvol]
  exact measure_mono hsub

theorem koebe_c_le_one (k G : ℂ → ℂ) (m : ℂ → ℂ) (c : ℂ)
    (hk : DifferentiableOn ℂ k (Metric.ball 0 1))
    (hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2))
    (hGinj : Set.InjOn G (Metric.ball (0 : ℂ) 1 \ {0}))
    (hG' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
      HasDerivAt G (-(((z ^ 2))⁻¹) + m z) z)
    (hm : DifferentiableOn ℂ m (Metric.ball (0 : ℂ) 1))
    (hm0 : m 0 = c)
    (hc : c = k 0)
    (hmeas : Measurable
      (fun z : ℂ => ENNReal.ofReal (‖-(((z ^ 2))⁻¹) + m z‖ ^ 2))) :
    ‖c‖ ≤ 1 := by
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    norm_num
  · by_contra hcon
    rw [not_le] at hcon
    have hcpos : (0 : ℝ) < ‖c‖ := lt_trans (by norm_num) hcon
    have ha0 : (0 : ℝ) ≤ ‖c‖⁻¹ := inv_nonneg.mpr (norm_nonneg c)
    have ha1 : ‖c‖⁻¹ < 1 := by
      have h1 := mul_lt_mul_of_pos_left hcon (inv_pos.mpr hcpos)
      rwa [mul_one, inv_mul_cancel₀ hcpos.ne'] at h1
    set r := (‖c‖⁻¹ + 1) / 2 with hrdef
    have hr0 : (0 : ℝ) < r := by
      rw [hrdef]
      linarith
    have hr1 : r < 1 := by
      rw [hrdef]
      linarith
    have hr2a : ‖c‖⁻¹ < r ^ 2 := by
      have h1a : (0 : ℝ) < 1 - ‖c‖⁻¹ := by linarith
      have hsq : (0 : ℝ) < (1 - ‖c‖⁻¹) ^ 2 := pow_pos h1a 2
      have e : r ^ 2 - ‖c‖⁻¹ = (1 - ‖c‖⁻¹) ^ 2 / 4 := by
        rw [hrdef]
        ring
      linarith
    have hcs : (1 : ℝ) < ‖c‖ * r ^ 2 := by
      have h1 : ‖c‖ * ‖c‖⁻¹ < ‖c‖ * r ^ 2 :=
        mul_lt_mul_of_pos_left hr2a hcpos
      rwa [mul_inv_cancel₀ hcpos.ne'] at h1
    have hkey : (1 : ℝ) < ‖c‖ ^ 2 * r ^ 4 := by
      have e1 : ‖c‖ ^ 2 * r ^ 4 = (‖c‖ * r ^ 2) ^ 2 := by ring
      rw [e1]
      have hlt := pow_lt_pow_left₀ hcs (by norm_num) two_ne_zero
      rwa [one_pow] at hlt
    have hrne : r ≠ 0 := ne_of_gt hr0
    have hδe : (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) * r ^ 2
        = ‖c‖ ^ 2 * r ^ 4 - 1 := by
      have hr1inv : r ^ 2 * r⁻¹ ^ 2 = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ hrne, one_pow]
      linear_combination -hr1inv
    have hδ : (0 : ℝ) < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
      have harg : (0 : ℝ) < (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) * r ^ 2 := by
        rw [hδe]
        linarith [hkey]
      exact pos_of_mul_pos_left harg (le_of_lt (pow_pos hr0 2))
    obtain ⟨M, hM, hk1⟩ := koebe_dslope_bound k hk
    have hM0 : (0 : ℝ) ≤ M := le_trans (by norm_num) hM
    have hGdiff : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 →
        DifferentiableAt ℂ G z :=
      fun z hz hzne => (hG' z hz hzne).differentiableAt
    set B := 8 * M + 16 * M ^ 2 + 1 with hBdef
    have hBpos : (0 : ℝ) < B := by
      rw [hBdef]
      have h1 : (0 : ℝ) ≤ 8 * M := by linarith
      have h2 : (0 : ℝ) ≤ 16 * M ^ 2 := by positivity
      linarith
    set ρ := min (min (1 / 2) (r / 2))
      (min (1 / (2 * (‖c‖ + 1)))
        ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B))) with hρdef
    have hρ0 : 0 < ρ := by
      rw [hρdef]
      refine lt_min (lt_min (by norm_num) (by linarith [hr0])) (lt_min ?_ ?_)
      · exact div_pos (by norm_num) (by linarith [norm_nonneg c])
      · exact div_pos hδ (by linarith [hBpos])
    have hρ2 : ρ ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
    have hρr : ρ < r := lt_of_le_of_lt
      (le_trans (min_le_left _ _) (min_le_right _ _)) (by linarith [hr0])
    have hρ1 : ρ ≤ 1 := le_trans hρ2 (by norm_num)
    have hρB : ρ ≤ (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hρc : ‖c‖ * ρ ^ 2 ≤ 1 / 2 := by
      have h1 : ρ ≤ 1 / (2 * (‖c‖ + 1)) :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      have h2 : (0 : ℝ) < 2 * (‖c‖ + 1) := by linarith [norm_nonneg c]
      have h3 : ρ * (2 * (‖c‖ + 1)) ≤ 1 := (le_div_iff₀ h2).mp h1
      have h4 : ρ * ‖c‖ ≤ 1 / 2 := by linarith [h3]
      have h5 : ‖c‖ * ρ ^ 2 = (ρ * ‖c‖) * ρ := by ring
      have h6 : (ρ * ‖c‖) * ρ ≤ (1 / 2) * ρ :=
        mul_le_mul_of_nonneg_right h4 hρ0.le
      have h7 : (1 / 2 : ℝ) * ρ ≤ 1 / 2 := by linarith [hρ2]
      linarith [h5, h6, h7]
    have hDnn : 0 ≤ ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 := by
      have hdet := koebeEll_det_abs ρ c hρ0
        (lt_of_le_of_lt hρc (by norm_num))
      rw [← hdet]
      exact abs_nonneg _
    have hDe : ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2 ≤ ρ⁻¹ ^ 2 := by
      linarith [mul_nonneg (sq_nonneg ‖c‖) (sq_nonneg ρ)]
    have hεnn : (0 : ℝ) ≤ 4 * M * ρ ^ 4 :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (pow_nonneg hρ0.le 4)
    have hU0 : (0 : ℝ) ≤ Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
        (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      mul_nonneg
        (mul_nonneg (le_of_lt Real.pi_pos) (sq_nonneg _)) hDnn
    have hlow := koebe_area_lower G m c ρ r hρ0 hρr hr1 hG' hGinj hm hm0
      hmeas
    have hup := koebe_volume_upper k G c ρ r M hk hG hGinj hGdiff hc hM hk1
      hρ0 hρ2 hρc hρr hr1
    have hboth : ENNReal.ofReal
          (Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2))
        ≤ ENNReal.ofReal (Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) :=
      le_trans hlow hup
    have hreal : Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2)
          + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        ≤ Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      (ENNReal.ofReal_le_ofReal_iff hU0).mp hboth
    have hLfactor : Real.pi * (ρ⁻¹ ^ 2 - r⁻¹ ^ 2)
          + Real.pi * ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        = Real.pi * ((ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)) := by
      ring
    have hUfactor : Real.pi * (1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        = Real.pi * ((1 + 4 * M * ρ ^ 4) ^ 2 *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)) := by
      ring
    rw [hLfactor, hUfactor] at hreal
    have hdiv : (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        ≤ (1 + 4 * M * ρ ^ 4) ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) :=
      le_of_mul_le_mul_left hreal Real.pi_pos
    have hLHS : (ρ⁻¹ ^ 2 - r⁻¹ ^ 2) + ‖c‖ ^ 2 * (r ^ 2 - ρ ^ 2)
        = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) + (‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) := by
      ring
    have hstep : (1 + 4 * M * ρ ^ 4) ^ 2 * (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        = (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
          + (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
            (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) := by
      ring
    rw [hLHS, hstep] at hdiv
    have hδ1 : ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2
        ≤ (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2) := by
      linarith
    have h2εnn : (0 : ℝ) ≤ 2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2 :=
      add_nonneg (mul_nonneg (by norm_num) hεnn) (sq_nonneg _)
    have hδ2 : (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) *
          (ρ⁻¹ ^ 2 - ‖c‖ ^ 2 * ρ ^ 2)
        ≤ (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) * ρ⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_left hDe h2εnn
    have hδ3 : (2 * (4 * M * ρ ^ 4) + (4 * M * ρ ^ 4) ^ 2) * ρ⁻¹ ^ 2
        = 8 * M * ρ ^ 2 + 16 * M ^ 2 * ρ ^ 6 := by
      have hρne : ρ ≠ 0 := ne_of_gt hρ0
      field_simp
      ring
    have hδle : ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2
        ≤ 8 * M * ρ ^ 2 + 16 * M ^ 2 * ρ ^ 6 := by
      rw [← hδ3]
      exact le_trans hδ1 hδ2
    have hBM0 : (0 : ℝ) ≤ 8 * M + 16 * M ^ 2 := by
      have h1 : (0 : ℝ) ≤ 8 * M := by linarith
      have h2 : (0 : ℝ) ≤ 16 * M ^ 2 := by positivity
      linarith
    have hρ6 : ρ ^ 6 ≤ ρ ^ 2 := pow_le_pow_of_le_one hρ0.le hρ1
      (by norm_num)
    have hρ2le : ρ ^ 2 ≤ ρ := by
      rw [pow_two]
      have h := mul_le_mul_of_nonneg_right hρ1 hρ0.le
      rwa [one_mul] at h
    have g1 : 16 * M ^ 2 * ρ ^ 6 ≤ 16 * M ^ 2 * ρ ^ 2 :=
      mul_le_mul_of_nonneg_left hρ6 (by positivity)
    have g2 : (8 * M + 16 * M ^ 2) * ρ ^ 2 ≤ (8 * M + 16 * M ^ 2) * ρ :=
      mul_le_mul_of_nonneg_left hρ2le hBM0
    have hfin : (8 * M + 16 * M ^ 2) * ρ < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
      have h1 : (8 * M + 16 * M ^ 2) * ρ
          ≤ (8 * M + 16 * M ^ 2) *
            ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B)) :=
        mul_le_mul_of_nonneg_left hρB hBM0
      have hBB : 8 * M + 16 * M ^ 2 < 2 * B := by
        rw [hBdef]
        linarith [sq_nonneg M, hM0]
      have hBpos2 : (0 : ℝ) < 2 * B := by linarith [hBpos]
      have h2 : (8 * M + 16 * M ^ 2) *
            ((‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2) / (2 * B))
          < ‖c‖ ^ 2 * r ^ 2 - r⁻¹ ^ 2 := by
        rw [← mul_div_assoc, div_lt_iff₀ hBpos2]
        have h3 := mul_lt_mul_of_pos_right hBB hδ
        linarith
      linarith
    linarith [hδle, g1, g2, hfin]

theorem koebe_bieberbach
    (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) 1))
    (hginj : Set.InjOn g (Metric.ball (0 : ℂ) 1))
    (hg0 : g 0 = 0)
    (hgderiv : deriv g 0 = 1) :
    ‖iteratedDeriv 2 g 0‖ ≤ 4 := by
  obtain ⟨s, hs, hs0, hsne, heq⟩ :=
    exists_sqrt_of_univalent g hg hginj hg0 hgderiv
  obtain ⟨hk, hkinv, hk0⟩ := koebe_inv_sqrt_expansion s hs hs0 hsne
  set k : ℂ → ℂ := dslope (fun w => (s w)⁻¹) 0 with hkdef
  set G : ℂ → ℂ := fun z => z⁻¹ + z * k (z ^ 2) with hGdef
  have hG : ∀ z : ℂ, G z = z⁻¹ + z * k (z ^ 2) := fun z => rfl
  obtain ⟨hsqmem, hGinv, hGne, hGinj⟩ :=
    koebe_G_injOn g s k G hsne heq hkinv hG hginj
  obtain ⟨hu, hm, hm0, hG'⟩ := koebe_G_hasDerivAt k G hk hG
  have hm' : DifferentiableOn ℂ (deriv (fun z : ℂ => z * k (z ^ 2)))
      (Metric.ball 0 1) := hm
  have hm0' : deriv (fun z : ℂ => z * k (z ^ 2)) 0 = k 0 := hm0
  have hG'' : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → HasDerivAt G
      (-(((z ^ 2))⁻¹) + deriv (fun z : ℂ => z * k (z ^ 2)) z) z := hG'
  have hmeasF : Measurable (fun z : ℂ => ENNReal.ofReal
      (‖-(((z ^ 2))⁻¹) + deriv (fun w : ℂ => w * k (w ^ 2)) z‖ ^ 2)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.add ((continuous_pow 2).measurable.inv).neg
    exact measurable_deriv _
  have hcle := koebe_c_le_one k G (deriv (fun z : ℂ => z * k (z ^ 2)))
    (k 0) hk hG hGinj hG'' hm' hm0' rfl hmeasF
  have hds := deriv_sqrt_eq_iteratedDeriv_two g s hs hs0 heq
  have e : iteratedDeriv 2 g 0 = -((4 : ℂ) * k 0) := by
    have e1 : iteratedDeriv 2 g 0 = 4 * deriv s 0 := by
      rw [hds]
      ring
    have e2 : deriv s 0 = -k 0 := by
      rw [hk0]
      ring
    rw [e1, e2]
    ring
  have h4 : ‖(4 : ℂ) * k 0‖ = 4 * ‖k 0‖ := by
    rw [norm_mul]
    congr 1
    norm_num
  rw [e, norm_neg, h4]
  linarith [hcle]

/--
If `f : ℂ → ℂ` is holomorphic and injective on `ball (0:ℂ) 1` with `f 0 = 0` and `deriv f 0 = 1`,
then `ball (0:ℂ) (1/4 : ℝ) ⊆ f '' ball (0:ℂ) 1`. Source: Koebe quarter theorem, conjectured by
P. Koebe in 1907 and proved by L. Bieberbach, Sitzungsberichte der Preussischen Akademie der
Wissenschaften (1916), 940–955; see Pommerenke, Univalent Functions; Lean is normalized schlicht
inclusion ball (0:ℂ) (1/4) ⊆ f '' ball 0 1.

Proves `Wanted` entry `koebe_quarter`.
-/
theorem koebe_quarter
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hinj : Set.InjOn f (Metric.ball (0 : ℂ) 1))
    (h0 : f 0 = 0)
    (hderiv : deriv f 0 = 1) :
    Metric.ball (0 : ℂ) (1/4 : ℝ) ⊆ f '' Metric.ball (0 : ℂ) 1 := by
  exact koebe_of_bieberbach koebe_bieberbach f hf hinj h0 hderiv

end Complex.KoebeQuarterWanted
end
