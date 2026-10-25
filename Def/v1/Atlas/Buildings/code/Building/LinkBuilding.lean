/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuilding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Link
import Lemma.Finset.Disjoint.of.In_FacesLinkComplex.In_Faces
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.IsMaximalUnion.of.IsMaximalLinkComplex.In_Faces
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Theorem.v1.Atlas.Buildings.code.Building.LinkBuildingIsoHelper
import Lemma.Finset.IsMaximalLinkComplex.of.IsMaximalUnion.In_FacesLinkComplex.In_Faces
import Lemma.Finset.IsFacetToSimplicialComplexAndIsMaximalToSimplicialComplex.Unique.of.IsMaximalToSimplicialComplex.IsFacetToSimplicialComplex.IsThin
import Lemma.Finset.IsMaximalToSimplicialComplexToChamberComplexUnion.of.IsMaximalLinkComplexToSimplicialComplexToChamberComplex.In_FacesToSimplicialComplexToChamberComplex
import Theorem.v1.Atlas.Buildings.code.Building.LinkBuilding
open scoped Classical


variable {V : Type} [DecidableEq V]


/-- The *link building*: the link $\mathrm{lk}_K(\sigma)$ of a face $\sigma$ of a building, equipped
with the apartment system consisting of links of ambient apartments, is itself a building. -/
noncomputable def link_building (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C) :
    Building V :=
  let K := b.toChamberComplex.toSimplicialComplex
  let lk := K.linkComplex σ hσ
  let link_apts : Set (SimplicialComplex V) :=
    {L | ∃ A ∈ b.apartmentSystem.apartments, ∃ (hσA : σ ∈ A.faces),
      L = A.linkComplex σ hσA}
  let link_cc : ChamberComplex V :=
    { toSimplicialComplex := lk
      exists_maximal := link_exists_maximal b σ hσ hσ_proper
      gallery_connected := link_gallery_connected b σ hσ hσ_proper }
  { toChamberComplex := link_cc
    apartmentSystem :=
    { apartments := link_apts
      nonempty_apartments := by
        obtain ⟨A, hA⟩ := b.apartmentSystem.nonempty_apartments
        obtain ⟨C, hC_max, hσ_sub⟩ := hσ_proper
        obtain ⟨B, hB_apt, hC_B, _⟩ := b.apartmentSystem.contains_pair C C hC_max hC_max
        have hσB : σ ∈ B.faces :=
          B.down_closed hC_B hσ_sub.1 (K.nonempty_of_mem σ hσ)
        exact ⟨B.linkComplex σ hσB, B, hB_apt, hσB, rfl⟩
      sub := by
        intro L hL
        obtain ⟨A, hA_apt, hσA, rfl⟩ := hL
        exact SimplicialComplex.linkComplex_sub (b.apartmentSystem.sub A hA_apt) σ hσ hσA
      contains_pair := by
        intro C' D' hC'_max hD'_max
        exact link_contains_pair b σ hσ link_apts rfl C' D' hC'_max hD'_max
      iso_exists := link_iso_exists b σ hσ hσ_proper link_apts rfl
      maximal_in_apt_is_maximal :=
        link_maximal_in_apt_is_maximal b σ hσ hσ_proper link_apts rfl
      gallery_convex :=
        link_gallery_convex b σ hσ hσ_proper link_cc rfl link_apts rfl
      building_maximal_in_apt_is_apt_maximal :=
        link_building_maximal_in_apt_is_apt_maximal b σ hσ hσ_proper link_apts rfl
      apt_nonempty := link_apt_nonempty b σ hσ hσ_proper link_apts rfl
      iso_bijective := link_iso_bijective b σ hσ hσ_proper link_apts rfl
      apt_is_coxeter := link_apt_is_coxeter b σ hσ hσ_proper link_apts rfl }
    thick := by
      intro F' C' hF'C' hC'_max
      exact link_is_thick b σ hσ F' C' hF'C' hC'_max }

