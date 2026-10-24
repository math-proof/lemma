/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptFoldingFromRetraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Retraction
import Lemma.Finset.IsMaximal.of.IsMaximalToSimplicialComplex.In_Faces.In_Apartments
import sympy.atlas.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments

open scoped Classical

variable {V : Type} [DecidableEq V]

namespace AptFoldingFromRetraction

/-- Adjacent chambers have the same cardinality. -/
theorem card_eq_of_adjacent {K : SimplicialComplex V} {C D : Finset V}
    (hadj : K.Adjacent C D) : C.card = D.card := by
  obtain ⟨_, _, _, F, hFC, hFD⟩ := hadj
  have hFC_sub : F ⊆ C := hFC.1.2.2
  have hFD_sub : F ⊆ D := hFD.1.2.2
  have hC_diff : (C \ F).card = 1 := hFC.2
  have hD_diff : (D \ F).card = 1 := hFD.2
  have h1 := Finset.card_sdiff_add_card_inter C F
  have h2 := Finset.card_sdiff_add_card_inter D F
  rw [Finset.inter_eq_right.mpr hFC_sub] at h1
  rw [Finset.inter_eq_right.mpr hFD_sub] at h2
  omega

/-- If a function $f$ is constant along every step of a chain under $R$, then $f$ agrees at the head and last of the chain. -/
theorem list_chain_preserves {α : Type*} {R : α → α → Prop}
    {f : α → ℕ} (hR : ∀ a b, R a b → f a = f b)
    : ∀ (l : List α) (hl : l ≠ []) (_ : List.IsChain R l),
    f (l.head hl) = f (l.getLast hl) := by
  intro l
  induction l with
  | nil => intro hl; exact absurd rfl hl
  | cons hd tl ih =>
    intro _hl hchain
    match tl, ih with
    | [], _ => rfl
    | hd' :: tl', ih =>
      simp only [List.head_cons]
      rw [List.getLast_cons (show (hd' :: tl') ≠ [] from List.cons_ne_nil _ _)]
      rw [List.isChain_cons] at hchain
      have hadj : R hd hd' := by apply hchain.1; simp [List.head?]
      calc f hd = f hd' := hR hd hd' hadj
        _ = f ((hd' :: tl').getLast (List.cons_ne_nil _ _)) :=
            ih (List.cons_ne_nil _ _) hchain.2

/-- Chambers connected by a gallery have the same cardinality. -/
theorem card_eq_of_gallery {K : SimplicialComplex V}
    {C D : Finset V} (g : Gallery K) (hconn : g.Connects C D) :
    C.card = D.card := by
  have hne : g.chambers ≠ [] := by
    intro h
    have : g.chambers.head? = some C := hconn.1
    rw [h] at this
    exact absurd this (by simp)
  have hpres := list_chain_preserves
    (fun a b h => card_eq_of_adjacent h)
    g.chambers hne g.adjacent_consecutive
  have hC : C = g.chambers.head hne := by
    have := hconn.1; rw [List.head?_eq_some_head hne] at this; exact (Option.some_injective _ this).symm
  have hD : D = g.chambers.getLast hne := by
    have := hconn.2; rw [List.getLast?_eq_some_getLast hne] at this; exact (Option.some_injective _ this).symm
  rw [hC, hD]; exact hpres

/-- A retraction fixing vertices of $A$ acts as the identity on faces of $A$. -/
theorem retraction_fixes_face
    {A : SimplicialComplex V}
    {ρ : V → V}
    (hρ_fix : ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v)
    {s : Finset V} (hs : s ∈ A.faces) :
    s.image ρ = s := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rwa [hρ_fix w ⟨s, hs, hw⟩]
  · intro hv
    exact ⟨v, hv, hρ_fix v ⟨s, hs, hv⟩⟩

/-- Thickness yields a third chamber: given adjacent chambers $C, C'$ sharing facet $F$, there
exists $E \notin \{C, C'\}$ also sharing the facet $F$. -/
theorem third_chamber_from_thickness
    {K : ChamberComplex V} (hthick : K.IsThick)
    {C C' : Finset V} (hadj : K.toSimplicialComplex.Adjacent C C') :
    ∃ E F, E ≠ C ∧ E ≠ C' ∧
      K.toSimplicialComplex.IsMaximal E ∧
      K.toSimplicialComplex.IsFacet F C ∧
      K.toSimplicialComplex.IsFacet F C' ∧
      K.toSimplicialComplex.IsFacet F E := by
  obtain ⟨hC_max, _, _, F, hF_C, hF_C'⟩ := hadj
  obtain ⟨D₁, D₂, hD₁_ne_C, hD₂_ne_C, hD₁₂_ne, hFD₁, hD₁_max, hFD₂, hD₂_max⟩ :=
    hthick F C hF_C hC_max
  by_cases h₁ : D₁ = C'
  · exact ⟨D₂, F, hD₂_ne_C, fun h => hD₁₂_ne (h₁ ▸ h.symm), hD₂_max,
          hF_C, hF_C', hFD₂⟩
  · exact ⟨D₁, F, hD₁_ne_C, h₁, hD₁_max, hF_C, hF_C', hFD₁⟩
