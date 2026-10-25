/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.KFinite.Part3
import Lemma.Complex.IsKFinite0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Def.v1.Atlas.LieGroups.code.SchurLemma
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Def.v1.Atlas.LieGroups.code.KFiniteProps.Part2


noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

variable {M : Type uM} [Ring M] [Algebra ℂ M] [TopologicalSpace M]

variable [CompactlySupportedMeasureAlgebra G M]

theorem isotypicComponent_hasOrthogonalProjection
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G E) (K : Subgroup G) [CompactSpace K]
    (σ : ContinuousRep K Wσ) :
    (IsotypicComponent π K σ).HasOrthogonalProjection := by
  by_cases hirr : σ.IsIrreducible
  ·

    let P := schurProjector π K σ hirr

    have hPidem : IsIdempotentElem P := by
      rw [IsIdempotentElem, ContinuousLinearMap.ext_iff]
      intro v
      simp only [ContinuousLinearMap.mul_apply]
      exact schurProjector_fixes_isotypic π K σ hirr (P v)
        (schurProjector_range_isotypic π K σ hirr v)

    have hrange : P.range = IsotypicComponent π K σ := by
      ext v
      constructor
      · rintro ⟨w, rfl⟩
        exact schurProjector_range_isotypic π K σ hirr w
      · intro hv
        exact ⟨v, schurProjector_fixes_isotypic π K σ hirr v hv⟩

    have hclosed : IsClosed (IsotypicComponent π K σ : Set E) := by
      rw [show (IsotypicComponent π K σ : Set E) = (P.range : Set E)
        from by rw [hrange]]
      exact ContinuousLinearMap.IsIdempotentElem.isClosed_range hPidem

    haveI : CompleteSpace (IsotypicComponent π K σ) :=
      hclosed.completeSpace_coe
    exact Submodule.HasOrthogonalProjection.ofCompleteSpace _
  ·


    have hbot : IsotypicComponent π K σ = ⊥ := by
      unfold IsotypicComponent
      rw [sSup_eq_bot]
      intro W hW
      obtain ⟨hWinv, hWirr, ⟨e⟩⟩ := hW


      exfalso; apply hirr

      intro U hU_inv
      let T := e.toContinuousLinearEquiv
      let U' : Submodule ℂ W := U.comap T.toLinearEquiv.toLinearMap
      have hU'_inv : ((π.restrictSubgroup K).subrepresentation W hWinv).IsInvariantSubspace U' := by
        constructor
        · exact hU_inv.isClosed.preimage T.continuous
        · intro g v hv
          show T.toLinearEquiv.toLinearMap
            (((π.restrictSubgroup K).subrepresentation W hWinv).toMonoidHom g v) ∈ U
          have hint : (T : W →L[ℂ] Wσ)
            (((π.restrictSubgroup K).subrepresentation W hWinv).toMonoidHom g v) =
            σ.toMonoidHom g (T v) := by
            have := ContinuousLinearMap.ext_iff.mp (e.intertwines g) v
            simp at this
            exact this
          rw [show T.toLinearEquiv.toLinearMap
            (((π.restrictSubgroup K).subrepresentation W hWinv).toMonoidHom g v) =
            (T : W →L[ℂ] Wσ)
            (((π.restrictSubgroup K).subrepresentation W hWinv).toMonoidHom g v) from rfl]
          rw [hint]
          exact hU_inv.invariant g (T v) hv
      rcases hWirr U' hU'_inv with h | h
      · left
        rw [Submodule.eq_bot_iff]
        intro w hw
        have hmem : T.symm w ∈ U' := by
          show T.toLinearEquiv.toLinearMap (T.symm w) ∈ U
          simp [ContinuousLinearEquiv.apply_symm_apply]
          exact hw
        rw [Submodule.eq_bot_iff] at h
        have := h _ hmem
        simp at this
        exact this
      · right
        rw [Submodule.eq_top_iff']
        intro w
        have hmem : T.symm w ∈ U' := by rw [h]; trivial
        have : T.toLinearEquiv.toLinearMap (T.symm w) ∈ U := hmem
        simp [ContinuousLinearEquiv.apply_symm_apply] at this
        exact this
    rw [hbot]
    exact Submodule.HasOrthogonalProjection.ofCompleteSpace ⊥

end Unitary
end ContinuousRep
end
