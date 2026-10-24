import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.Infinity.Sectors
open ChamberComplex AffineBuilding


/--
[SectorInfrastructure.sector_chamber_cover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
@[path]
private lemma main
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b} :
-- imply
  ∀ (S : Sector b), ∀ v ∈ S.vertices, ∃ D ∈ S.apartment.faces, S.apartment.IsMaximal D ∧ v ∈ D ∧ ∀ w ∈ D, w ∈ S.vertices := by
-- proof
  intro S v hv
  obtain ⟨s, hs_face, hv_in_s⟩ := S.vertices_in_apartment v hv
  obtain ⟨D, hD_face, hD_max, hs_sub_D⟩ :=
    si.apt_face_extends_to_chamber S.apartment S.apartment_mem s hs_face
  have hv_in_D : v ∈ D := hs_sub_D hv_in_s
  have hD_in_S : ∀ w ∈ D, w ∈ S.vertices :=
    si.sector_chamber_closed S D hD_face hD_max ⟨v, hv_in_D, hv⟩
  exact ⟨D, hD_face, hD_max, hv_in_D, hD_in_S⟩



/--
[SectorInfrastructure.sector_chambers_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.sector_chambers_transfer
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {_si : SectorInfrastructure b}
  {S : Sector b}
  {A : SimplicialComplex V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : ∃ C, C ∈ A.faces ∧ S.apartment.IsMaximal C ∧ ∀ v ∈ C, v ∈ S.vertices)
  (hD : D ∈ S.apartment.faces)
  (hD_max : S.apartment.IsMaximal D)
  (hD_in_S : ∀ w ∈ D, w ∈ S.vertices) :
-- imply
  D ∈ A.faces := by
-- proof
  obtain ⟨C, hC_A, hC_max_apt, _⟩ := hC
  have hC_bldg_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C :=
    b.apartmentSystem.maximal_in_apt_is_maximal S.apartment S.apartment_mem C hC_max_apt
  exact apt_faces_subset b A S.apartment hA S.apartment_mem C hC_A hC_max_apt.1 hC_bldg_max hD



/--
[SectorInfrastructure.sector_has_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.sector_has_chamber
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b} :
-- imply
  ∀ (S : Sector b), ∃ C, C ∈ S.apartment.faces ∧ S.apartment.IsMaximal C ∧ ∀ v ∈ C, v ∈ S.vertices := by
-- proof
  intro S
  obtain ⟨v, hv⟩ := S.nonempty
  obtain ⟨D, hD_face, hD_max, _, hD_in_S⟩ := si.sector_chamber_cover S v hv
  exact ⟨D, hD_face, hD_max, hD_in_S⟩



/--
[SectorInfrastructure.sector_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.sector_transfer
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {S : Sector b}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : ∃ C, C ∈ A.faces ∧ S.apartment.IsMaximal C ∧ ∀ v ∈ C, v ∈ S.vertices) :
-- imply
  SetInApartment A S.vertices := by
-- proof
  intro v hv
  obtain ⟨D, hD_face, hD_max, hv_D, hD_in_S⟩ := si.sector_chamber_cover S v hv
  have hD_in_A : D ∈ A.faces :=
    si.sector_chambers_transfer S A hA hC D hD_face hD_max hD_in_S
  exact ⟨D, hD_in_A, hv_D⟩



/--
[SectorInfrastructure.cone_vertex_subsector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.cone_vertex_subsector
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {_si : SectorInfrastructure b}
  {S : Sector b}
  {v : V}
-- given
  (hv : v ∈ S.vertices) :
-- imply
  ∃ (S' : Sector b), S'.apartment = S.apartment ∧ S'.baseVertex = v ∧ S'.vertices ⊆ S.vertices := by
-- proof
  refine ⟨⟨S.apartment, S.apartment_mem, v,
    S.vertices_in_apartment v hv, S.vertices, S.vertices_in_apartment,
    hv, S.nonempty⟩, rfl, rfl, Set.Subset.refl _⟩



/--
[SectorInfrastructure.iso_from_shared_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.iso_from_shared_chamber
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {_si : SectorInfrastructure b}
  {A A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hA' : A' ∈ b.apartmentSystem.apartments)
  (hC_A : C ∈ A.faces)
  (hC_A' : C ∈ A'.faces)
  (hC_max : A.IsMaximal C) :
-- imply
  ∃ φ : SimplicialMap A A', ∀ v ∈ C, φ.toFun v = v := by
-- proof
  obtain ⟨φ, _, hfix_C⟩ :=
    b.apartmentSystem.iso_exists A hA A' hA' C hC_A hC_A' C hC_max hC_A'
  exact ⟨φ, hfix_C⟩



/--
[SectorInfrastructure.chamber_sector_common_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.chamber_sector_common_apartment
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {C : Finset V}
  {S : Sector b}
-- given
  (hC : b.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments ∧ C ∈ A.faces ∧ ∃ (S' : Sector b), Sector.Subsector b S' S ∧ SetInApartment A S'.vertices := by
-- proof
  obtain ⟨D, hD_face, hD_max, hD_in_S⟩ := si.sector_has_chamber S
  have hD_bmax : b.toSimplicialComplex.IsMaximal D :=
    b.apartmentSystem.maximal_in_apt_is_maximal S.apartment S.apartment_mem D hD_max
  obtain ⟨A, hA_mem, hC_in_A, hD_in_A⟩ :=
    b.apartmentSystem.contains_pair C D hC hD_bmax
  have hS_in_A : SetInApartment A S.vertices := by
    apply si.sector_transfer S A hA_mem
    exact ⟨D, hD_in_A, hD_max, hD_in_S⟩
  exact ⟨A, hA_mem, hC_in_A, S, ⟨Set.Subset.refl _, S, S, Set.Subset.refl _, Set.Subset.refl _, rfl⟩, hS_in_A⟩



/--
[SectorInfrastructure.sectors_any_common_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma SectorInfrastructure.sectors_any_common_apartment
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {S₁ S₂ : Sector b} :
-- imply
  ∃ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments ∧ SetInApartment A S₁.vertices ∧ SetInApartment A S₂.vertices := by
-- proof
  obtain ⟨C₁, hC₁_face, hC₁_max, hC₁_in_S₁⟩ := si.sector_has_chamber S₁
  obtain ⟨C₂, hC₂_face, hC₂_max, hC₂_in_S₂⟩ := si.sector_has_chamber S₂
  have hC₁_bmax : b.toSimplicialComplex.IsMaximal C₁ :=
    b.apartmentSystem.maximal_in_apt_is_maximal S₁.apartment S₁.apartment_mem C₁ hC₁_max
  have hC₂_bmax : b.toSimplicialComplex.IsMaximal C₂ :=
    b.apartmentSystem.maximal_in_apt_is_maximal S₂.apartment S₂.apartment_mem C₂ hC₂_max
  obtain ⟨A, hA_mem, hC₁_in_A, hC₂_in_A⟩ :=
    b.apartmentSystem.contains_pair C₁ C₂ hC₁_bmax hC₂_bmax
  have hS₁_in_A : SetInApartment A S₁.vertices := by
    apply si.sector_transfer S₁ A hA_mem
    exact ⟨C₁, hC₁_in_A, hC₁_max, hC₁_in_S₁⟩
  have hS₂_in_A : SetInApartment A S₂.vertices := by
    apply si.sector_transfer S₂ A hA_mem
    exact ⟨C₂, hC₂_in_A, hC₂_max, hC₂_in_S₂⟩
  exact ⟨A, hA_mem, hS₁_in_A, hS₂_in_A⟩



/--
[Sector.SameDirection.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma Sector.SameDirection.refl
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b} :
-- imply
  Sector.SameDirection b S S :=
-- proof
  ⟨S, S, Set.Subset.refl _, Set.Subset.refl _, rfl⟩



/--
[Sector.SameDirection.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma Sector.SameDirection.symm
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S₁ S₂ : Sector b}
-- given
  (h : Sector.SameDirection b S₁ S₂) :
-- imply
  Sector.SameDirection b S₂ S₁ := by
-- proof
  obtain ⟨T₁, T₂, hT₁, hT₂, hTeq⟩ := h
  exact ⟨T₂, T₁, hT₂, hT₁, hTeq.symm⟩



/--
[Sector.Subsector.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma Sector.Subsector.refl
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {S : Sector b} :
-- imply
  Sector.Subsector b S S :=
-- proof
  ⟨Set.Subset.refl _, Sector.SameDirection.refl b S⟩



/--
[sectors_any_common_apartment'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma sectors_any_common_apartment'
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {S₁ S₂ : Sector b} :
-- imply
  ∃ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments ∧ SetInApartment A S₁.vertices ∧ SetInApartment A S₂.vertices :=
-- proof
  si.sectors_any_common_apartment S₁ S₂


/--
[apt_face_extends_to_chamber_of_building](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean)
-/
private lemma apt_face_extends_to_chamber_of_building_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V} :
-- imply
  ∀ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments → ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D := by
-- proof
  apply AffineBuilding.apt_face_extends_to_chamber_of_building b


-- created on 2026-10-23
-- updated on 2026-10-24
