/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Lemma.Finset.GalleryDist.le.Length.of.Connects
import Def.v1.Atlas.Buildings.code.Building.Labels
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.EqImageRefl.of.Ne.EqImageToFun.EqImageToFun.IsMaximalToSimplicialComplex
import Theorem.v1.Atlas.Buildings.code.Building.VertexActionHelper
set_option maxHeartbeats 0

open scoped Classical

set_option maxHeartbeats 0


variable {V : Type} [DecidableEq V]


/-- Strict inclusion is preserved by the image of an injective function on
finite sets. -/
theorem finset_image_ssubset_of_injective {f : V → V} (hf : Function.Injective f)
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

/-- For any pair of chambers $C, D$ of an apartment $A$, there exists a
bijective vertex map (apartment automorphism) sending $C$ to $D$. -/
theorem apt_automorphism_sending_chamber
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (D : Finset V) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C := by

  obtain ⟨B_idx, M, cc, hcc, φ, hinj, hsurj, hadj, hThin⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA

  have hCox : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
      (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
      (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
      (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :=
    ⟨B_idx, M, φ, hinj, hsurj, hadj⟩

  have hWR : ∀ C D : Finset V, A.Adjacent C D →
      ∃ wr : ChamberComplex.WallReflection cc, D.image wr.refl = C :=
    coxeter_apt_wall_reflections cc A hcc hThin hCox

  exact ChamberComplex.apt_vertex_level_automorphism A cc hcc hWR C D hC hD

/-- A bijective vertex map between apartments that preserves the face
structure is label-preserving. -/
theorem bijective_face_iso_preserves_maximal
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

