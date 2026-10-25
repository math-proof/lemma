import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
open scoped Classical


/--
[building_maximal_of_apt_contains_all](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/RetractionOntoApartment.lean)
-/
@[path]
lemma building_maximal_of_apt_contains_all
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
  (hD : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
-- imply
  A.IsMaximal D := by
-- proof
  constructor
  · exact h_all D hD.1
  · intro y hy hDy
    have hy_bldg : y ∈ b.toChamberComplex.toSimplicialComplex.faces :=
      b.apartmentSystem.sub A hA hy
    exact hD.2 y hy_bldg hDy

private lemma building_adj_of_apt_contains_all
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
  (hadj : b.toChamberComplex.toSimplicialComplex.Adjacent C D) :
-- imply
  A.Adjacent C D := by
-- proof
  obtain ⟨hC_max, hD_max, hne, F, hFC, hFD⟩ := hadj
  refine ⟨building_maximal_of_apt_contains_all b A hA h_all hC_max,
    building_maximal_of_apt_contains_all b A hA h_all hD_max,
    hne, F, ?_, ?_⟩
  · exact ⟨⟨h_all F hFC.1.1, h_all C hC_max.1, hFC.1.2.2⟩, hFC.2⟩
  · exact ⟨⟨h_all F hFD.1.1, h_all D hD_max.1, hFD.1.2.2⟩, hFD.2⟩

private lemma apt_maximal_of_building_contains_all
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
  (hD : A.IsMaximal D) :
-- imply
  b.toChamberComplex.toSimplicialComplex.IsMaximal D := by
-- proof
  constructor
  · exact b.apartmentSystem.sub A hA hD.1
  · intro y hy hDy
    exact hD.2 y (h_all y hy) hDy

private lemma apt_adj_of_building_contains_all
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces)
  (hadj : A.Adjacent C D) :
-- imply
  b.toChamberComplex.toSimplicialComplex.Adjacent C D := by
-- proof
  obtain ⟨hC_max, hD_max, hne, F, hFC, hFD⟩ := hadj
  have hC_bldg := apt_maximal_of_building_contains_all b A hA h_all hC_max
  have hD_bldg := apt_maximal_of_building_contains_all b A hA h_all hD_max
  refine ⟨hC_bldg, hD_bldg, hne, F, ?_, ?_⟩
  · exact ⟨⟨b.apartmentSystem.sub A hA hFC.1.1,
    b.apartmentSystem.sub A hA hC_max.1, hFC.1.2.2⟩, hFC.2⟩
  · exact ⟨⟨b.apartmentSystem.sub A hA hFD.1.1,
    b.apartmentSystem.sub A hA hD_max.1, hFD.1.2.2⟩, hFD.2⟩

private lemma canonical_BuildingRetraction
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_A : C ∈ A.faces)
  (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃ (ρ : BuildingRetraction b), ρ.apt = A ∧ ρ.base = C ∧ (C.image ρ.map = C) ∧ (∀ B ∈ b.apartmentSystem.apartments, C ∈ B.faces → Function.Injective ρ.map ∧ (∀ s, s ∈ B.faces ↔ s.image ρ.map ∈ A.faces)) ∧ (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ.map = s) := by
-- proof
  obtain ⟨ρ, hρ_simp, hρ_fix, hρ_C, hρ_iso, hρ_id⟩ :=
    exists_canonical_retraction b A hA C hC_A hC_max
  have h_all : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces := by
    intro s hs; have := hρ_simp s hs; rwa [hρ_id s hs] at this
  have hC_max_A : A.IsMaximal C :=
    building_maximal_of_apt_contains_all b A hA h_all hC_max
  refine ⟨{
    apt := A
    apt_mem := hA
    base := C
    base_maximal := hC_max_A
    map := ρ
    map_face := hρ_simp
    map_fixes := hρ_fix
    map_chamber := fun D hD_max => by
      rw [hρ_id D hD_max.1]
      exact building_maximal_of_apt_contains_all b A hA h_all hD_max
    map_adj_or_eq := fun D E hDE => by
      rw [hρ_id D hDE.1.1, hρ_id E hDE.2.1.1]
      exact Or.inr (building_adj_of_apt_contains_all b A hA h_all hDE)
  }, rfl, rfl, hρ_C, hρ_iso, hρ_id⟩


-- created on 2026-10-24
