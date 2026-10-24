/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KFiniteProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.KFinite
import Lemma.Complex.IsKFinite0
import Lemma.Fin.Any_Eq_SMul.of.All_ToMonoidHom.IsIrreducible
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import sympy.atlas.v1.Atlas.LieGroups.code.SchurLemma
import sympy.atlas.v1.Atlas.LieGroups.code.Admissible
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

noncomputable section

open scoped ComplexOrder

universe uG uM

namespace ContinuousRep

variable {G : Type uG} [Group G] [TopologicalSpace G]

section KStability

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

theorem kFiniteSubspace_stable (π : ContinuousRep G V) (K : Subgroup G)
    (g : K) (v : V) (hv : v ∈ kFiniteSubspace π K) :
    (π.toMonoidHom g) v ∈ kFiniteSubspace π K := by
  rw [mem_kFiniteSubspace] at hv ⊢
  unfold IsKFinite at *
  have hsub : Submodule.span ℂ
      (Set.range (fun k : K => (π.toMonoidHom k) ((π.toMonoidHom g) v))) ≤
      Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx
    show (π.toMonoidHom k) ((π.toMonoidHom g) v) ∈
      (Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) : Set V)
    have heq : (π.toMonoidHom k) ((π.toMonoidHom g) v) =
        (π.toMonoidHom ((k : G) * (g : G))) v := by
      rw [← ContinuousLinearMap.mul_apply]; congr 1
      exact (π.toMonoidHom.map_mul (k : G) (g : G)).symm
    rw [heq]
    exact Submodule.subset_span ⟨⟨(k : G) * (g : G), K.mul_mem k.2 g.2⟩, rfl⟩
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

end KStability

section Unitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unitary_adjoint_eq_inv (π : ContinuousRep G E) (hU : π.IsUnitary)
    (g : G) :
    ContinuousLinearMap.adjoint (π.toMonoidHom g) = π.toMonoidHom g⁻¹ := by
  have h1 := (hU g).1
  have hginv : π.toMonoidHom g * π.toMonoidHom g⁻¹ = 1 := by
    rw [← map_mul]; simp
  calc ContinuousLinearMap.adjoint (π.toMonoidHom g)
      = ContinuousLinearMap.adjoint (π.toMonoidHom g) * 1 := (mul_one _).symm
    _ = ContinuousLinearMap.adjoint (π.toMonoidHom g) *
        (π.toMonoidHom g * π.toMonoidHom g⁻¹) := by rw [hginv]
    _ = (ContinuousLinearMap.adjoint (π.toMonoidHom g) * π.toMonoidHom g) *
        π.toMonoidHom g⁻¹ := (mul_assoc _ _ _).symm
    _ = 1 * π.toMonoidHom g⁻¹ := by rw [h1]
    _ = π.toMonoidHom g⁻¹ := one_mul _

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

omit [TopologicalSpace G] in
def discreteMeasureRep (π : G →* (V →L[ℂ] V)) :
    MonoidAlgebra ℂ G →ₐ[ℂ] (V →L[ℂ] V) :=
  MonoidAlgebra.lift ℂ (V →L[ℂ] V) G π

class CompactlySupportedMeasureAlgebra
    (G : Type uG) [Group G] [TopologicalSpace G]
    (M : Type uM) [Ring M] [Algebra ℂ M] [TopologicalSpace M] where
  dirac : G →* M
  discrete_in_closure : ∀ (m : M),
    m ∈ closure (Set.range (MonoidAlgebra.lift ℂ M G dirac))
  total_variation_cont : ∀ (f : G → ℝ) (_hf : Continuous f) (_hf_nn : ∀ g, 0 ≤ f g),
    @Continuous (MonoidAlgebra ℂ G) ℝ
      (TopologicalSpace.induced
        (MonoidAlgebra.lift ℂ M G dirac)
        ‹TopologicalSpace M›)
      inferInstance
      (fun μ => μ.sum (fun g c => ‖c‖ * f g))

@[reducible]
def weakTopologyOnDiscreteMeasures :
    TopologicalSpace (MonoidAlgebra ℂ G) :=
  TopologicalSpace.induced
    (MonoidAlgebra.lift ℂ M G CompactlySupportedMeasureAlgebra.dirac)
    ‹TopologicalSpace M›

def IsKFiniteFunc (K : Subgroup G) (f : ↥K → ℂ) : Prop :=
  FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun g : ↥K => fun k : ↥K => f (g⁻¹ * k))))

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

instance isotypicComponent_instHasOrthogonalProjection
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G E) (K : Subgroup G) [CompactSpace K]
    (σ : ContinuousRep K Wσ) :
    (IsotypicComponent π K σ).HasOrthogonalProjection :=
  isotypicComponent_hasOrthogonalProjection π K σ

noncomputable def isotypicProjection
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (π : ContinuousRep G E) (K : Subgroup G) [CompactSpace K]
    (σ : ContinuousRep K Wσ) :
    E →L[ℂ] E :=
  (IsotypicComponent π K σ).subtypeL.comp
    (IsotypicComponent π K σ).orthogonalProjection
