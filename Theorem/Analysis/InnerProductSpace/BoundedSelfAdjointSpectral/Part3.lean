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
public import Instance.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral
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

theorem spectralMul_integral_measure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℝ)) :
    ∫ z, f z ∂spectralMulMeasure T hT v =
      Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
        (⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ :
          C(spectrum ℂ T, ℂ)) v) v) :=
  (hT.exists_spectralMeasure T v).choose_spec.2.2 f

end
