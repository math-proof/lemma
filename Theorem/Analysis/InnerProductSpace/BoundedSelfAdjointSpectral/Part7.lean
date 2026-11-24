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
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part7
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
