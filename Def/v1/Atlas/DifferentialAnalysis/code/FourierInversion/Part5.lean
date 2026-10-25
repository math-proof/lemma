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
import Theorem.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part4
open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap


noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

variable {n : ℕ}

/-- Given an `L²` function `f`, construct the element of `H^s` whose witness
function is `f`: namely, `𝓕⁻¹ (⟨ξ⟩^{-s} f)` as a tempered distribution. -/
def Hs.fromL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs n s := by

  set w : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹


  set v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
    TemperedDistribution.smulLeftCLM ℂ w (Lp.toTemperedDistribution f)

  set u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) := 𝓕⁻ v

  have hmem : MemHs n s u := by
    refine ⟨↑↑f, Lp.memLp f, fun φ => ?_⟩

    have hFu : 𝓕 u = v := FourierInversion.fourier_inverse_right v
    rw [hFu]


    simp only [v, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply]


    have hw_temp : w.HasTemperateGrowth := by
      show (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth

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
    simp only [smul_eq_mul, w]
    ring
  exact ⟨u, hmem⟩

end Isomorphism
end FourierInversion
end
