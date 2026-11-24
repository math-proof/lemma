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
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part16
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

theorem spectralMulGlobalLpOperator_ae
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (g : Lp ℂ 2 (spectralMulSumMeasure T hT)) :
    spectralMulGlobalLpOperator T hT g =ᵐ[spectralMulSumMeasure T hT]
      fun x => (x.2 : ℂ) * g x := by
  change (spectralMulGlobalCoordinateLp T hT • g :
    Lp ℂ 2 (spectralMulSumMeasure T hT)) =ᵐ[spectralMulSumMeasure T hT] _
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulGlobalCoordinateLp T hT) g,
    spectralMulGlobalCoordinateLp_ae T hT] with x hmul hx
  rw [hmul]
  change (spectralMulGlobalCoordinateLp T hT) x * g x = (x.2 : ℂ) * g x
  rw [hx]
  rfl

theorem spectralMulGlobalLpOperator_fiber
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (i : spectralMulIndexSet T hT)
    (g : Lp ℂ 2 (spectralMulMeasure T hT (i : E))) :
    spectralMulGlobalLpOperator T hT (spectralMulFiberIsometry T hT i g) =
      spectralMulFiberIsometry T hT i (spectralMulLpOperator T hT (i : E) g) := by
  apply Lp.ext
  filter_upwards [spectralMulGlobalLpOperator_ae T hT
      (spectralMulFiberIsometry T hT i g),
    MemLp.coeFn_toLp (spectralMulExtend_memLp T hT i g),
    MemLp.coeFn_toLp
      (spectralMulExtend_memLp T hT i (spectralMulLpOperator T hT (i : E) g)),
    spectralMulExtend_congr_ae T hT i (spectralMulLpOperator_ae T hT (i : E) g)]
      with x hmul hg hMg hcongr
  rw [hmul]
  change (x.2 : ℂ) *
      ((((spectralMulExtend_memLp T hT i g).toLp
        (spectralMulExtend T hT i g)) : spectralMulSpace T hT → ℂ) x) =
    ((((spectralMulExtend_memLp T hT i (spectralMulLpOperator T hT (i : E) g)).toLp
        (spectralMulExtend T hT i (spectralMulLpOperator T hT (i : E) g))) :
          spectralMulSpace T hT → ℂ) x)
  rw [hg, hMg, hcongr]
  by_cases hx : x ∈ spectralMulFiber T hT i
  · simp [spectralMulExtend, Set.indicator_of_mem hx]
  · simp [spectralMulExtend, Set.indicator_of_notMem hx]

end
