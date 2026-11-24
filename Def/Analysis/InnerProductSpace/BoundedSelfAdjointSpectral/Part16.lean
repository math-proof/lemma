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
public import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part15
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

noncomputable def spectralMulGlobalLpOperator
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    Lp ℂ 2 (spectralMulSumMeasure T hT) →L[ℂ]
      Lp ℂ 2 (spectralMulSumMeasure T hT) :=
  LinearMap.mkContinuous
    { toFun := fun g => spectralMulGlobalCoordinateLp T hT • g
      map_add' := fun g₁ g₂ => Lp.add_smul _ _ _
      map_smul' := fun c g => by
        change spectralMulGlobalCoordinateLp T hT • (c • g) =
          c • (spectralMulGlobalCoordinateLp T hT • g)
        exact (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
          (spectralMulGlobalCoordinateLp T hT) g).symm }
    ‖spectralMulGlobalCoordinateLp T hT‖
    (fun g => Lp.norm_smul_le (spectralMulGlobalCoordinateLp T hT) g)

end
