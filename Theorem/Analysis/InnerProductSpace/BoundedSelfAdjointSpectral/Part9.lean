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
import Def.Analysis.InnerProductSpace.BoundedSelfAdjointSpectral.Part9
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
