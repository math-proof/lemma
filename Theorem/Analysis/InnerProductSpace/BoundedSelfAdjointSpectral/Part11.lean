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
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part11
open MeasureTheory
open scoped CompactlySupported ComplexOrder ENNReal


public section

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Multiplication form of the spectral theorem

This file constructs scalar spectral measures for bounded self-adjoint operators, realizes their
cyclic subspaces as `L²` spaces, and combines a maximal orthogonal family of cyclic subspaces into
the multiplication-operator form of the spectral theorem.
-/
noncomputable section

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

universe u

theorem spectralMulFiber_measurableSet
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    MeasurableSet (spectralMulFiber T hT i) := by
  exact (measurable_fst (β := spectrum ℂ T) (α := spectralMulIndexSet T hT))
    (MeasurableSet.singleton i)

theorem spectralMulSumMeasure_restrict_fiber
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT) :
    (spectralMulSumMeasure T hT).restrict (spectralMulFiber T hT i) =
      spectralMulFiberMeasure T hT i := by
  ext s hs
  rw [Measure.restrict_apply hs,
    spectralMulSumMeasure, Measure.sum_apply _ (hs.inter (spectralMulFiber_measurableSet T hT i))]
  classical
  rw [tsum_eq_single i]
  · rw [spectralMulFiberMeasure, Measure.map_apply measurable_prodMk_left
      (hs.inter (spectralMulFiber_measurableSet T hT i)),
      Measure.map_apply measurable_prodMk_left hs]
    congr 1
    ext z
    simp [spectralMulFiber]
  · intro j hji
    rw [spectralMulFiberMeasure, Measure.map_apply measurable_prodMk_left
      (hs.inter (spectralMulFiber_measurableSet T hT i))]
    simp [spectralMulFiber, hji]

end
