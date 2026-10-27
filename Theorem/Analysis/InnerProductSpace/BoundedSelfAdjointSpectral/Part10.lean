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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part10
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

theorem spectralMulIndexSet_admissible
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    spectralMulAdmissible T hT (spectralMulIndexSet T hT) :=
  (spectralMul_exists_maximalAdmissible T hT).choose_spec.1

theorem spectralMulIndexSet_maximal
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (S : Set E)
    (hS : spectralMulAdmissible T hT S)
    (hsub : spectralMulIndexSet T hT ⊆ S) : spectralMulIndexSet T hT = S :=
  (spectralMul_exists_maximalAdmissible T hT).choose_spec.2 S hS hsub

theorem spectralMulIndexSet_total
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    (⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E))ᗮ = ⊥ := by
  let K := ⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E)
  rw [Submodule.eq_bot_iff]
  intro w hw
  by_contra hw0
  have hadd : spectralMulAdmissible T hT (insert w (spectralMulIndexSet T hT)) := by
    rw [spectralMulAdmissible, Set.pairwise_insert]
    refine ⟨spectralMulIndexSet_admissible T hT, ?_⟩
    intro v hvS hwv
    have hZvK : spectralMulCyclicSubspace T hT v ≤ K :=
      le_iSup (fun i : spectralMulIndexSet T hT =>
        spectralMulCyclicSubspace T hT (i : E)) ⟨v, hvS⟩
    have hwZv : w ∈ (spectralMulCyclicSubspace T hT v)ᗮ :=
      (Submodule.orthogonal_le hZvK) hw
    have h := spectralMulCyclicSubspace_isOrtho T hT hwZv
    exact ⟨h, h.symm⟩
  have heq := spectralMulIndexSet_maximal T hT _ hadd
    (Set.subset_insert w (spectralMulIndexSet T hT))
  have hwS : w ∈ spectralMulIndexSet T hT := by
    rw [heq]
    exact Set.mem_insert w _
  have hwK : w ∈ K :=
    (le_iSup (fun i : spectralMulIndexSet T hT =>
      spectralMulCyclicSubspace T hT (i : E)) ⟨w, hwS⟩)
      (spectralMul_mem_cyclicSubspace T hT w)
  exact hw0 (inner_self_eq_zero.mp ((Submodule.mem_orthogonal K w).mp hw w hwK))

theorem spectralMulOrthogonalFamily
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    OrthogonalFamily ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (fun i => spectralMulCyclicIsometry T hT (i : E)) := by
  intro i j hij x y
  have h := spectralMulIndexSet_admissible T hT i.property j.property
    (Subtype.coe_ne_coe.mpr hij)
  exact h.inner_eq (LinearMap.mem_range_self _ x) (LinearMap.mem_range_self _ y)

theorem spectralMulIsHilbertSum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    IsHilbertSum ℂ
      (fun i : spectralMulIndexSet T hT => Lp ℂ 2 (spectralMulMeasure T hT (i : E)))
      (fun i => spectralMulCyclicIsometry T hT (i : E)) := by
  apply IsHilbertSum.mk (spectralMulOrthogonalFamily T hT)
  let K := ⨆ i : spectralMulIndexSet T hT, spectralMulCyclicSubspace T hT (i : E)
  have hK : Kᗮ = ⊥ := spectralMulIndexSet_total T hT
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, hK, Submodule.bot_orthogonal_eq_top]
  rw [show (⨆ i : spectralMulIndexSet T hT,
      LinearMap.range (spectralMulCyclicIsometry T hT (i : E)).toLinearMap) = K from rfl,
    hclosure]

end
