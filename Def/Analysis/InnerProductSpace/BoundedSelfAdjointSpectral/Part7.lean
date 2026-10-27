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
import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part6
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
