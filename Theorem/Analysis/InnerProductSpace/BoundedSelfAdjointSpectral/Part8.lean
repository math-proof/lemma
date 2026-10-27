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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part8
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

theorem spectralMul_cfc_mem_cyclicSubspace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℂ T, ℂ)) :
    (cfcHom hT.isStarNormal) f v ∈ spectralMulCyclicSubspace T hT v := by
  exact ⟨ContinuousMap.toLp 2 (spectralMulMeasure T hT v) ℂ f,
    spectralMulCyclicIsometry_toLp T hT v f⟩

theorem spectralMul_mem_cyclicSubspace
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    v ∈ spectralMulCyclicSubspace T hT v := by
  simpa using spectralMul_cfc_mem_cyclicSubspace T hT v (1 : C(spectrum ℂ T, ℂ))

theorem spectralMulCyclicSubspace_isOrtho
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) {v w : E}
    (hw : w ∈ (spectralMulCyclicSubspace T hT v)ᗮ) :
    spectralMulCyclicSubspace T hT w ⟂ spectralMulCyclicSubspace T hT v := by
  rw [Submodule.isOrtho_iff_le]
  rintro _ ⟨g, rfl⟩
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT w) ℂ
    (by norm_num)).induction ?_
      ((spectralMulCyclicSubspace T hT v).isClosed_orthogonal.preimage
        (spectralMulCyclicIsometry T hT w).continuous) g
  rintro _ ⟨f, rfl⟩
  change spectralMulCyclicIsometry T hT w
    (ContinuousMap.toLp 2 (spectralMulMeasure T hT w) ℂ f) ∈ _
  rw [spectralMulCyclicIsometry_toLp]
  apply (Submodule.mem_orthogonal' (spectralMulCyclicSubspace T hT v) _).mpr
  rintro _ ⟨q, rfl⟩
  change inner ℂ ((cfcHom hT.isStarNormal) f w)
    (spectralMulCyclicIsometry T hT v q) = 0
  refine (ContinuousMap.toLp_denseRange ℂ (spectralMulMeasure T hT v) ℂ
    (by norm_num)).induction ?_
      (isClosed_eq (continuous_const.inner (spectralMulCyclicIsometry T hT v).continuous)
        continuous_const) q
  rintro _ ⟨k, rfl⟩
  rw [spectralMulCyclicIsometry_toLp]
  let A := (cfcHom hT.isStarNormal) f
  let B := (cfcHom hT.isStarNormal) k
  calc
    inner ℂ (A w) (B v) = inner ℂ w (ContinuousLinearMap.adjoint A (B v)) :=
      (ContinuousLinearMap.adjoint_inner_right A w (B v)).symm
    _ = inner ℂ w ((cfcHom hT.isStarNormal) (star f * k) v) := by
      rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
    _ = 0 := (Submodule.mem_orthogonal' (spectralMulCyclicSubspace T hT v) w).mp hw _
      (spectralMul_cfc_mem_cyclicSubspace T hT v (star f * k))

end
