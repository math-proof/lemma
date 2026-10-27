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
import Theorem.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral
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

def spectralMulOfRealL (X : Type*) [TopologicalSpace X] :
    C(X, ℝ) →ₗ[ℝ] C(X, ℂ) where
  toFun := spectralMulOfReal
  map_add' f g := by
    ext x
    simp
  map_smul' r f := by
    ext x
    simp

noncomputable def spectralMulFunctional
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    C_c((spectrum ℂ T), ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f =>
        Complex.re (inner ℂ ((cfcHom hT.isStarNormal)
          (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) v) v)
      map_add' := by
        intro f g
        have hfg : spectralMulOfRealL (spectrum ℂ T) (f + g).toContinuousMap =
            spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap +
              spectralMulOfRealL (spectrum ℂ T) g.toContinuousMap := by
          ext x
          change (((f + g) x : ℝ) : ℂ) = (f x : ℂ) + (g x : ℂ)
          simp
        rw [hfg, map_add, add_apply, inner_add_left]
        exact Complex.add_re _ _
      map_smul' := by
        intro r f
        have hrf : spectralMulOfRealL (spectrum ℂ T) (r • f).toContinuousMap =
            (r : ℂ) • spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap := by
          ext x
          change (((r • f) x : ℝ) : ℂ) = (r : ℂ) * (f x : ℂ)
          simp
        rw [hrf, map_smul, smul_apply, inner_smul_left]
        simp }
    (fun f hf => by
      have hfc : 0 ≤ spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap := by
        intro x
        exact Complex.zero_le_real.mpr (hf x)
      have hop : 0 ≤ (cfcHom hT.isStarNormal)
          (spectralMulOfRealL (spectrum ℂ T) f.toContinuousMap) :=
        (cfcHom_nonneg_iff hT.isStarNormal).mpr hfc
      exact (ContinuousLinearMap.nonneg_iff_isPositive.mp hop).re_inner_nonneg_left v)

end
