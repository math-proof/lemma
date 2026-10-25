import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.Infinity.SectorGallery
open ChamberComplex AffineBuilding


/--
[simplicial_map_apt_preserves_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/SectorGallery.lean)
-/
@[path]
lemma simplicial_map_apt_preserves_maximal
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A' : SimplicialComplex V}
  {A : SimplicialComplex V}
  {ρ : SimplicialMap A' A}
  {C : Finset V}
-- given
  (_hA' : A' ∈ b.apartmentSystem.apartments)
  (_hA : A ∈ b.apartmentSystem.apartments)
  (_hC : C ∈ A'.faces)
  (_hC_max : A'.IsMaximal C) :
-- imply
  A.IsMaximal (Finset.image ρ.toFun C) := by
-- proof
  let 𝒜 := b.apartmentSystem
  let bldgSC := b.toChamberComplex.toSimplicialComplex
  let φ : Finset V → Finset V := fun s => s.image ρ.toFun
  let S₁ : Set (Finset V) := {C}
  have hφ_into_A : ∀ C₁ ∈ S₁, φ C₁ ∈ A.faces := by
    intro C₁ hC₁
    have h := Set.eq_of_mem_singleton hC₁
    rw [h]
    exact ρ.map_face C _hC
  have hφ_dist : ∀ C₁ ∈ S₁, ∀ D ∈ S₁,
    galleryDist bldgSC (φ C₁) (φ D) = galleryDist bldgSC C₁ D := by
    intro C₁ hC₁ D hD
    rw [Set.eq_of_mem_singleton hC₁, Set.eq_of_mem_singleton hD]
    simp [galleryDist_self]
  exact (galleryDist_preserving_maps_to_maximal 𝒜 A _hA S₁ φ hφ_into_A hφ_dist C
    (Set.mem_singleton C)).1


private lemma retraction_image_properties
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A' : SimplicialComplex V}
  {A : SimplicialComplex V}
  {ρ : SimplicialMap A' A}
  {D₀ : Finset V}
  {D : Finset V}
  {D' : Finset V}
  {F : Finset V}
-- given
  (_hA' : A' ∈ b.apartmentSystem.apartments)
  (_hA : A ∈ b.apartmentSystem.apartments)
  (_hD₀ : D₀ ∈ A'.faces)
  (_hD₀_max : A'.IsMaximal D₀)
  (_hD : D ∈ A'.faces)
  (_hD_max : A'.IsMaximal D)
  (_hD' : D' ∈ A'.faces)
  (_hD'_max : A'.IsMaximal D')
  (_hF : F ∈ A'.faces)
  (_hF_sub_D₀ : F ⊆ D₀)
  (_hF_sub_D : F ⊆ D)
  (_hF_sub_D' : F ⊆ D') :
-- imply
  A.IsMaximal (Finset.image ρ.toFun D₀) ∧ A.IsMaximal (Finset.image ρ.toFun D) ∧ A.IsMaximal (Finset.image ρ.toFun D') ∧ Finset.image ρ.toFun F ∈ A.faces := by
-- proof
  exact ⟨simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D₀ _hD₀ _hD₀_max,
    simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D _hD _hD_max,
    simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D' _hD' _hD'_max,
    ρ.map_face F _hF⟩


-- created on 2026-10-24
