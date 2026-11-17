/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Order.Zorn
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part2
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal

/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/

public section


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
