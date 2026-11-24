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
public import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part9
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

theorem spectralMul_exists_maximalAdmissible
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    ∃ S : Set E, spectralMulAdmissible T hT S ∧
      ∀ S' : Set E, spectralMulAdmissible T hT S' → S ⊆ S' → S = S' := by
  obtain ⟨S, hS⟩ := zorn_subset {S : Set E | spectralMulAdmissible T hT S} (by
    intro c hc hchain
    refine ⟨⋃₀ c, ?_, ?_⟩
    · rintro x hx y hy hxy
      obtain ⟨sx, hsxc, hxs⟩ := Set.mem_sUnion.mp hx
      obtain ⟨sy, hsyc, hys⟩ := Set.mem_sUnion.mp hy
      rcases hchain.total (x := sx) (y := sy) hsxc hsyc with hsxy | hsyx
      · exact (hc hsyc) (x := x) (hsxy hxs) (y := y) hys hxy
      · exact (hc hsxc) (x := x) hxs (y := y) (hsyx hys) hxy
    · intro s hs
      exact Set.subset_sUnion_of_mem hs)
  exact ⟨S, hS.prop, fun S' hS' hsub => hS.eq_of_le hS' hsub⟩

end
