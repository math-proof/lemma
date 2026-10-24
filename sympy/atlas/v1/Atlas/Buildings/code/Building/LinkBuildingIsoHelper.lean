/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuildingIsoHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Link
import Lemma.Finset.Disjoint.of.In_FacesLinkComplex.In_Faces
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.UniqueRetraction

open SimplicialComplex in
/-- If $\tau$ is a maximal face of the link $\mathrm{lk}_K(\sigma)$, then $\sigma \cup \tau$ is a
maximal face of the ambient complex $K$. -/
theorem union_maximal_of_linkComplex_maximal_helper {V : Type*} [DecidableEq V]
    {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_max : (K.linkComplex σ hσ).IsMaximal τ) :
    K.IsMaximal (σ ∪ τ) := by
  have hτ_link := hτ_max.1
  rw [mem_linkComplex_iff] at hτ_link
  refine ⟨hτ_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hτ_sub : τ ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hτ_link.2.1 hv⟩
    rw [hτ_max.2 (w \ σ) hw_link hτ_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hτ_link.1
    exact Finset.disjoint_right.mp hτ_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))

variable {V : Type} [DecidableEq V]

/-- Any two chambers $C, D$ of an apartment $A$ are related by a bijective automorphism of $A$
sending $D$ to $C$. -/
theorem apt_automorphism_sending_chamber'
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (D : Finset V) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C :=
  apt_automorphism_sending_chamber b A hA C hC D hD

/-- Pushing forward a strict inclusion of finite sets along an injective map yields a strict
inclusion of images. -/
theorem finset_image_ssubset_of_injective' {f : V → V} (hf : Function.Injective f)
    {s t : Finset V} (h : s ⊂ t) : s.image f ⊂ t.image f := by
  constructor
  · exact Finset.image_subset_image h.1
  · intro heq
    apply h.2
    intro x hx
    have : f x ∈ s.image f := by
      apply heq
      exact Finset.mem_image_of_mem f hx
    rw [Finset.mem_image] at this
    obtain ⟨y, hy, hfy⟩ := this
    have := hf hfy; subst this; exact hy

/-- A bijective simplicial isomorphism $\varphi : A \to A'$ carries maximal faces of $A$ to maximal
faces of $A'$. -/
theorem bijective_face_iso_preserves_maximal'
    {A A' : SimplicialComplex V} {φ : V → V} (hφ_bij : Function.Bijective φ)
    (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
    {s : Finset V} (hs : A.IsMaximal s) : A'.IsMaximal (s.image φ) := by
  constructor
  · exact (hφ_faces s).mp hs.1
  · intro t ht hsub
    set t₀ := t.preimage φ (hφ_bij.1.injOn) with ht₀_def
    have mem_t₀ : ∀ x, x ∈ t₀ ↔ φ x ∈ t := fun x => Finset.mem_preimage
    have ht₀_img : t₀.image φ = t := by
      ext z; constructor
      · rw [Finset.mem_image]; rintro ⟨w, hw, rfl⟩; exact (mem_t₀ w).mp hw
      · intro hz
        obtain ⟨w, rfl⟩ := hφ_bij.2 z
        exact Finset.mem_image_of_mem φ ((mem_t₀ w).mpr hz)
    have ht₀_face : t₀ ∈ A.faces := by
      rw [← ht₀_img] at ht; exact (hφ_faces t₀).mpr ht
    have hs_sub_t₀ : s ⊆ t₀ := by
      intro x hx; exact (mem_t₀ x).mpr (hsub (Finset.mem_image_of_mem φ hx))
    have hs_eq : s = t₀ := hs.2 t₀ ht₀_face hs_sub_t₀
    rw [← ht₀_img, ← hs_eq]

/-- For two apartments $B, B_0$ sharing a common chamber $D$, there is a bijective face-preserving
isomorphism $B \to B_0$ that fixes $D$ setwise. -/
theorem iso_bijective_fixing_chamber'
    (b : Building V)
    (B : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (B₀ : SimplicialComplex V) (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces) (hD_B₀ : D ∈ B₀.faces)
    (hD_max_B : B.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧
      D.image φ = D := by
  obtain ⟨ψ, hψ_bij, hψ_faces⟩ :=
    b.apartmentSystem.iso_bijective B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
  have hDψ_max_B₀ : B₀.IsMaximal (D.image ψ) :=
    bijective_face_iso_preserves_maximal' hψ_bij hψ_faces hD_max_B
  have hD_max_B₀ : B₀.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀
      (b.apartmentSystem.maximal_in_apt_is_maximal B hB D hD_max_B)
  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber' b B₀ hB₀ D hD_max_B₀ (D.image ψ) hDψ_max_B₀
  refine ⟨α ∘ ψ, hα_bij.comp hψ_bij, ?_, ?_⟩
  · intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hψ_faces s) (hα_faces (s.image ψ))
  · simp only [← Finset.image_image]
    exact hα_send

/-- By apartment-level unique labelling, any bijective face-preserving isomorphism $B \to B'$ that
fixes a chamber $D$ setwise acts as the identity on every face of $B$. -/
theorem bij_iso_fixing_chamber_is_id'
    (b : Building V)
    (B B' : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces)
    (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D)
    (φ : V → V) (hφ_bij : Function.Bijective φ)
    (hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
    (hφ_D : D.image φ = D) :
    ∀ s ∈ B.faces, s.image φ = s := by
  have hD_max_B : B.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
  have hmono_id : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t → s ⊂ t := by
    intro s t _ _ h; exact h
  have hmono_φ : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t →
      s.image φ ⊂ t.image φ := by
    intro s t _ _ hst
    exact finset_image_ssubset_of_injective' hφ_bij.1 hst
  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling B hB
    V V id (fun s => s.image φ) hmono_id hmono_φ D hD_max_B
  have h_agree_D : D.image φ = (id D).image (id : V → V) := by
    simp [hφ_D]
  intro s hs
  have := hprop id Function.bijective_id h_agree_D s hs
  simp at this
  exact this
