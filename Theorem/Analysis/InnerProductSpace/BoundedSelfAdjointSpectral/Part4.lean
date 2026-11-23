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
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part4

@[expose] public section

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

theorem spectralMulCfcMap_norm
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    ‖spectralMulCfcMap T hT v f‖ =
      ‖ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f‖ := by
  let A := (cfcHom hT.isStarNormal) f
  let q : C(spectrum ℂ T, ℝ) :=
    ⟨fun z => Complex.normSq (f z), Complex.continuous_normSq.comp f.continuous⟩
  have hq :
      (⟨fun z => (q z : ℂ), Complex.continuous_ofReal.comp q.continuous⟩ :
        C(spectrum ℂ T, ℂ)) = star f * f := by
    ext z
    exact Complex.normSq_eq_conj_mul_self
  have hm := spectralMul_integral_measure T hT v q
  rw [hq, map_mul, map_star] at hm
  have hadj : inner ℂ ((star A * A) v) v = inner ℂ (A v) (A v) := by
    rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  apply (sq_eq_sq₀ (norm_nonneg (spectralMulCfcMap T hT v f))
    (norm_nonneg (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f))).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (spectralMulCfcMap T hT v f),
    norm_sq_eq_re_inner (𝕜 := ℂ)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)]
  change (inner ℂ (spectralMulCfcMap T hT v f)
      (spectralMulCfcMap T hT v f)).re =
    (inner ℂ (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)
      (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)).re
  calc
    (inner ℂ (spectralMulCfcMap T hT v f)
        (spectralMulCfcMap T hT v f)).re =
        ∫ z, q z ∂spectralMulMeasure T hT v := by
      rw [show spectralMulCfcMap T hT v f = A v from rfl, ← hadj]
      exact hm.symm
    _ = (∫ z, f z * starRingEnd ℂ (f z) ∂spectralMulMeasure T hT v).re := by
      rw [show (fun z => f z * starRingEnd ℂ (f z)) =
          fun z => (q z : ℂ) by
        funext z
        exact Complex.mul_conj (f z)]
      have hi :
          (∫ z, (q z : ℂ) ∂spectralMulMeasure T hT v) =
            ((∫ z, q z ∂spectralMulMeasure T hT v : ℝ) : ℂ) := by
        exact integral_ofReal
      rw [hi]
      simp
    _ = (inner ℂ
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)
        (ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f)).re := by
      rw [MeasureTheory.ContinuousMap.inner_toLp]

end
