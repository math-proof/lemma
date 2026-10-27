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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part7
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

theorem spectralMulLpOperator_toLp
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    spectralMulLpOperator T hT v
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f) =
      ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ
        (spectralMulCoordinate T * f) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (p := ∞) (q := 2) (r := 2)
      (spectralMulCoordinateLp T hT v)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f),
    spectralMulCoordinateLp_ae T hT v,
    f.coeFn_toLp (p := 2) (𝕜 := ℂ) (spectralMulMeasure T hT v),
    (spectralMulCoordinate T * f).coeFn_toLp (p := 2) (𝕜 := ℂ)
      (spectralMulMeasure T hT v)] with z hmul hc hf hcf
  change _ = (spectralMulCoordinate T * f : C(spectrum ℂ T, ℂ)) z at hcf
  have hprod : (spectralMulCoordinateLp T hT v) z *
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f) z =
      (z : ℂ) * f z := congrArg₂ (· * ·) hc hf
  simpa [spectralMulLpOperator, spectralMulCoordinate, Pi.smul_apply, smul_eq_mul]
    using hmul.trans hprod |>.trans hcf.symm

theorem spectralMulCyclicIsometry_intertwines
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (g : Lp ℂ 2 (spectralMulMeasure T hT v)) :
    spectralMulCyclicIsometry T hT v (spectralMulLpOperator T hT v g) =
      T (spectralMulCyclicIsometry T hT v g) := by
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ
    (by norm_num)).induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) g
  rintro y ⟨f, rfl⟩
  rw [spectralMulLpOperator_toLp, spectralMulCyclicIsometry_toLp,
    spectralMulCyclicIsometry_toLp, map_mul, spectralMulCoordinate, cfcHom_id,
    mul_apply_eq_comp]

end
