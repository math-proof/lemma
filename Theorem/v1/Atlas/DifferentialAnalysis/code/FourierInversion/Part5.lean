/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part5
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- Right inverse: extracting the `L²` witness from `Hs.fromL2 s f` recovers
`f`. Uses Lebesgue uniqueness of integration against smooth, compactly
supported test functions to conclude the underlying functions are equal a.e. -/
theorem Hs.fromL2_witnessL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs.witnessL2 n s (Hs.fromL2 n s f) = f := by

  apply MeasureTheory.Lp.ext

  have h_wl2 : ↑↑(Hs.witnessL2 n s (Hs.fromL2 n s f)) =ᵐ[volume]
      Hs.witnessFunc n s (Hs.fromL2 n s f) :=
    MeasureTheory.MemLp.coeFn_toLp _

  refine h_wl2.trans ?_


  set u := Hs.fromL2 n s f
  set g₁ := Hs.witnessFunc n s u
  set g₂ : EuclideanSpace ℝ (Fin n) → ℂ := ↑↑f

  have hg₁_spec := Hs.witnessFunc_spec n s u

  have hg₂_spec : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ


    have hFu : 𝓕 u.1 = TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹)
        (MeasureTheory.Lp.toTemperedDistribution f) :=
      FourierInversion.fourier_inverse_right _
    rw [hFu]
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hw_temp : (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
      have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
          (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
        ext ξ
        simp only [sobolevWeight]
        rw [← Complex.ofReal_inv]
        congr 1
        exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
      rw [heq]
      apply Function.Complex.hasTemperateGrowth_ofReal.comp
      show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
      show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
      have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
        Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
      suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
          (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
        rw [h]; exact this
      ext ξ
      simp only [japaneseBracket]
      rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
      congr 1
      ring
    congr 1
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp]
    simp only [smul_eq_mul]
    ring

  have hint_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₁ ξ * φ ξ =
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ
    rw [← hg₁_spec φ, ← hg₂_spec φ]


  have hg₁_li : MeasureTheory.LocallyIntegrable g₁ volume :=
    (Hs.witnessFunc_memLp n s u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg₂_li : MeasureTheory.LocallyIntegrable g₂ volume :=
    (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_of_integral_contDiff_smul_eq hg₁_li hg₂_li
  intro g_test hg_smooth hg_supp


  have hw_htg : (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1; ring
  have hψ_smooth := hg_smooth.mul hw_htg.1
  have hψ_supp : HasCompactSupport (fun ξ => g_test ξ * sobolevWeight n s ξ) :=
    hg_supp.mul_right

  set φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hψ_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ_smooth)

  have key := hint_eq φ


  have heq_lhs : (fun x => g_test x • g₁ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  have heq_rhs : (fun x => g_test x • g₂ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  calc ∫ x, g_test x • g₁ x
      = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x := congr_arg _ heq_lhs
    _ = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x := key
    _ = ∫ x, g_test x • g₂ x := congr_arg _ heq_rhs.symm

/-- Left inverse: starting from a Sobolev distribution `u`, taking the
`L²` witness and then applying `Hs.fromL2` returns `u`. Uses Fourier
inversion on tempered distributions. -/
theorem Hs.witnessL2_fromL2 (s : ℝ) (u : Hs n s) :
    Hs.fromL2 n s (Hs.witnessL2 n s u) = u := by
  apply Subtype.ext

  simp only [Hs.fromL2, Hs.witnessL2]


  suffices h : (TemperedDistribution.smulLeftCLM ℂ
      (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u))) =
      𝓕 u.val by
    rw [h]
    exact FourierInversion.fourier_inverse_left u.val

  apply ContinuousLinearMap.ext
  intro φ


  have hw_temp : (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
    have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
        (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
      ext ξ
      simp only [sobolevWeight]
      rw [← Complex.ofReal_inv]
      congr 1
      exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
    rw [heq]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
    show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
    suffices hh : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
      rw [hh]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring


  trans (∫ ξ : EuclideanSpace ℝ (Fin n),
    (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ)
  ·
    show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      ∫ ξ : EuclideanSpace ℝ (Fin n),
        (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ
    rw [show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))
        (SchwartzMap.smulLeftCLM ℂ (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹) φ) from
      TemperedDistribution.smulLeftCLM_apply_apply _ _ _]
    rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    refine MeasureTheory.integral_congr_ae ?_
    have hae := MeasureTheory.MemLp.coeFn_toLp
      (f := Hs.witnessFunc n s u) (hf := Hs.witnessFunc_memLp n s u)
    filter_upwards [hae] with ξ hξ
    simp only [smul_eq_mul]
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp, smul_eq_mul, hξ]
    ring
  ·
    exact (Hs.witnessFunc_spec n s u φ).symm

end Isomorphism
end FourierInversion
end
