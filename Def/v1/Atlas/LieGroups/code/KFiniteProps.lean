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
import Theorem.v1.Atlas.LieGroups.code.KFiniteProps


noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def orthogonalProjection_intertwines_subrep
    (π : ContinuousRep G E) (hU : π.IsUnitary) (K : Subgroup G)
    (W₁ W₂ : Submodule ℂ E)
    (hW₁ : (π.restrictSubgroup K).IsInvariantSubspace W₁)
    (hW₂ : (π.restrictSubgroup K).IsInvariantSubspace W₂) :
    RepHom ((π.restrictSubgroup K).subrepresentation W₁ hW₁)
           ((π.restrictSubgroup K).subrepresentation W₂ hW₂) where
  toContinuousLinearMap :=


    haveI : CompleteSpace ↥W₂ := hW₂.isClosed.completeSpace_coe
    haveI : W₂.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W₂
    W₂.orthogonalProjection.comp W₁.subtypeL
  intertwines := by
    haveI : CompleteSpace ↥W₂ := hW₂.isClosed.completeSpace_coe
    haveI : W₂.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace W₂
    intro g
    ext ⟨v, hv⟩


    simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]


    have hcomm_val : (W₂.orthogonalProjection ((π.toMonoidHom (g : G)) v) : E) =
        (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) := by
      have h_mem : (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) ∈ W₂ :=
        hW₂.invariant g _ (W₂.orthogonalProjection v).2
      have h_orth : ∀ w ∈ W₂,
          @inner ℂ _ _ ((π.toMonoidHom (g : G)) v -
            (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E)) w = 0 := by
        intro w hw
        have heq : (π.toMonoidHom (g : G)) v -
            (π.toMonoidHom (g : G)) (W₂.orthogonalProjection v : E) =
            (π.toMonoidHom (g : G)) (v - (W₂.orthogonalProjection v : E)) := by
          rw [map_sub]
        rw [heq, ← ContinuousLinearMap.adjoint_inner_right,
            unitary_adjoint_eq_inv π hU (g : G)]
        exact Submodule.orthogonalProjectionFn_inner_eq_zero v _ (hW₂.invariant g⁻¹ w hw)
      rw [← Submodule.orthogonalProjectionFn_eq]
      exact Submodule.eq_orthogonalProjectionFn_of_mem_of_inner_eq_zero h_mem h_orth


    show (W₂.orthogonalProjection
      ((((π.restrictSubgroup K).subrepresentation W₁ hW₁).toMonoidHom g) ⟨v, hv⟩ : E) : E) =
      ((((π.restrictSubgroup K).subrepresentation W₂ hW₂).toMonoidHom g)
        (W₂.orthogonalProjection (v : E)) : E)

    simp only [subrepresentation, restrictSubgroup, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact hcomm_val

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
def discreteMeasureRep (π : G →* (V →L[ℂ] V)) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (V →L[ℂ] V) :=
  MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π

end Unitary
end ContinuousRep
end
