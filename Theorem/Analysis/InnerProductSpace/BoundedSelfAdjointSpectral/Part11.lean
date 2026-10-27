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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part11
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
