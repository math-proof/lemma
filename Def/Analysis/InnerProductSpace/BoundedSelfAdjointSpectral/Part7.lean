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
public import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part6
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

noncomputable def spectralMulLpOperator
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    Lp ℂ 2 (spectralMulMeasure T hT v) →L[ℂ]
      Lp ℂ 2 (spectralMulMeasure T hT v) :=
  LinearMap.mkContinuous
    { toFun := fun g => spectralMulCoordinateLp T hT v • g
      map_add' := fun g₁ g₂ => Lp.add_smul _ _ _
      map_smul' := fun c g => by
        change spectralMulCoordinateLp T hT v • (c • g) =
          c • (spectralMulCoordinateLp T hT v • g)
        exact (Lp.smul_comm (p := ∞) (q := 2) (r := 2) c
          (spectralMulCoordinateLp T hT v) g).symm }
    ‖spectralMulCoordinateLp T hT v‖
    (fun g => Lp.norm_smul_le (spectralMulCoordinateLp T hT v) g)

end
