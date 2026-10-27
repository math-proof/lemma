/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Order.Zorn
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part2
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal

/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/


noncomputable section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

universe u

@[simp] theorem spectralMulFunctional_apply
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C_c((spectrum ℂ T), ℝ)) :
    spectralMulFunctional T hT v f = Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
      (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) v) v) :=
  rfl

/-- A self-adjoint operator and a vector determine a finite regular scalar spectral measure.

The measure lives on the complex spectrum. Its support is real because the spectrum of a
self-adjoint operator is real. -/
theorem IsSelfAdjoint.exists_spectralMeasure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    ∃ μ : Measure (spectrum ℂ T), IsFiniteMeasure μ ∧ μ.Regular ∧
      ∀ f : C(spectrum ℂ T, ℝ),
        ∫ z, f z ∂μ = Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
          (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
            C(spectrum ℂ T, ℂ)) v) v) := by
  let Λ := spectralMulFunctional T hT v
  let μ := RealRMK.rieszMeasure Λ
  refine ⟨μ, inferInstance, inferInstance, ?_⟩
  intro f
  let f' : C_c((spectrum ℂ T), ℝ) :=
    CompactlySupportedContinuousMap.continuousMapEquiv f
  have h := RealRMK.integral_rieszMeasure Λ f'
  have hmap : spectralMulOfRealL (spectrum ℂ T) f'.toContinuousMap =
      (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
        C(spectrum ℂ T, ℂ)) := by
    ext z
    rfl
  rw [← hmap]
  simpa [μ, Λ, f'] using h

end
