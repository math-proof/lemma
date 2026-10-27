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
import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part15
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
