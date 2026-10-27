import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
open AffineBuilding


namespace AffineBuilding

/--
[pointsAtInfinity_eq_of_vertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
lemma pointsAtInfinity_eq_of_vertices_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {S₁ S₂ : Sector b}
-- given
  (hv : S₁.vertices = S₂.vertices) :
-- imply
  S₁.pointsAtInfinity md = S₂.pointsAtInfinity md := by
-- proof
  simp only [Sector.pointsAtInfinity]
  simp_rw [hv]

end AffineBuilding

namespace AffineBuilding

/--
[apartmentBoundary_coxeter_face_completeness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
lemma apartmentBoundary_coxeter_face_completeness
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {A : SimplicialComplex V}
  {σ : SimplexAtInfinity b md}
  {T : Set (PointAtInfinity b md)}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hσ : σ ∈ (apartmentBoundary b si md A hA).simplices)
  (hT_ne : T.Nonempty)
  (hT_sub : T ⊆ σ.points) :
-- imply
  ∃ (τ : SimplexAtInfinity b md), τ ∈ (apartmentBoundary b si md A hA).simplices ∧ τ.points = T := by
-- proof
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ
  refine ⟨⟨T, ⟨S, hT_sub.trans hS_pts⟩, hT_ne⟩, ?_, rfl⟩
  simp only [apartmentBoundary, Set.mem_setOf_eq]
  exact ⟨S, hS_apt, hT_sub.trans hS_pts⟩

end AffineBuilding

namespace AffineBuilding

/--
[apartment_boundary_maximal_face_in_set](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
lemma apartment_boundary_maximal_face_in_set
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {Ainf : ApartmentAtInfinity b md}
  {T : Set (PointAtInfinity b md)}
  {σ : SimplexAtInfinity b md}
-- given
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
  (hT_ne : T.Nonempty)
  (hT_from_sector : ∃ (S : Sector b), S.apartment = Ainf.apartment ∧ T ⊆ S.pointsAtInfinity md)
  (hσ : σ ∈ Ainf.simplices)
  (hσT : σ.points ⊆ T) :
-- imply
  ∃ (γ : SimplexAtInfinity b md), γ ∈ Ainf.simplices ∧ γ.points ⊆ T ∧ (∀ (δ : SimplexAtInfinity b md), δ ∈ Ainf.simplices → δ.points ⊆ T → δ.points ⊆ γ.points) := by
-- proof
  obtain ⟨S, hS_apt, hT_sub_S⟩ := hT_from_sector
  obtain ⟨A, hA, hAinf_eq⟩ := hAinf
  let γ : SimplexAtInfinity b md := ⟨T, ⟨S, hT_sub_S⟩, hT_ne⟩
  refine ⟨γ, ?_, fun x hx => hx, fun δ _ hδT => hδT⟩
  rw [hAinf_eq]
  simp only [apartmentBoundary, Set.mem_setOf_eq]
  have hS_apt' : S.apartment = A := by
    rw [hS_apt, hAinf_eq]; rfl
  exact ⟨S, hS_apt', hT_sub_S⟩

end AffineBuilding

namespace AffineBuilding

/--
[apartment_is_subcomplex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
lemma apartment_is_subcomplex
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {Ainf : ApartmentAtInfinity b md}
-- given
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
-- imply
  (buildBoundaryComplex b si md).IsSimplicialSubcomplex Ainf.simplices where subset :=
-- proof
  (apartment_simplices_sub b si md Ainf hAinf).1
    face_closed := (apartment_simplices_sub b si md Ainf hAinf).2

end AffineBuilding

/--
[SimplexAtInfinity.IsFace.refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma refl_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ : SimplexAtInfinity b md} :
-- imply
  SimplexAtInfinity.IsFace b md σ σ := by
-- proof
  apply AffineBuilding.SimplexAtInfinity.IsFace.refl b md σ

/--
[SimplexAtInfinity.IsFace.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma trans_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ τ ρ : SimplexAtInfinity b md}
-- given
  (h₁ : SimplexAtInfinity.IsFace b md σ τ)
  (h₂ : SimplexAtInfinity.IsFace b md τ ρ) :
-- imply
  SimplexAtInfinity.IsFace b md σ ρ := by
-- proof
  apply AffineBuilding.SimplexAtInfinity.IsFace.trans h₁ h₂

/--
[SimplexAtInfinity.IsFace.antisymm_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma antisymm_points_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ τ : SimplexAtInfinity b md}
-- given
  (h₁ : SimplexAtInfinity.IsFace b md σ τ)
  (h₂ : SimplexAtInfinity.IsFace b md τ σ) :
-- imply
  σ.points = τ.points := by
-- proof
  apply AffineBuilding.SimplexAtInfinity.IsFace.antisymm_points h₁ h₂

/--
[SimplexAtInfinity.ext'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma ext'_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {σ τ : SimplexAtInfinity b md}
-- given
  (h : σ.points = τ.points) :
-- imply
  σ = τ := by
-- proof
  apply AffineBuilding.SimplexAtInfinity.ext' h

/--
[apartment_simplices_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma apartment_simplices_sub_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {Ainf : ApartmentAtInfinity b md}
-- given
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
-- imply
  (Ainf.simplices ⊆ allSimplicesAtInfinity b si md) ∧ (∀ (σ τ : SimplexAtInfinity b md), σ ∈ Ainf.simplices → SimplexAtInfinity.IsFace b md τ σ → τ ∈ Ainf.simplices) := by
-- proof
  apply AffineBuilding.apartment_simplices_sub b si md Ainf hAinf

/--
[any_two_simplices_common_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma any_two_simplices_common_apartment_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {σ₁ : SimplexAtInfinity b md}
  {σ₂ : SimplexAtInfinity b md}
-- given
  (hσ₁ : σ₁ ∈ allSimplicesAtInfinity b si md)
  (hσ₂ : σ₂ ∈ allSimplicesAtInfinity b si md) :
-- imply
  ∃ Ainf ∈ allApartmentsAtInfinity b si md, σ₁ ∈ Ainf.simplices ∧ σ₂ ∈ Ainf.simplices := by
-- proof
  apply AffineBuilding.any_two_simplices_common_apartment b si md σ₁ hσ₁ σ₂ hσ₂

/--
[face_in_apartment_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean)
-/
@[path]
private lemma face_in_apartment_boundary_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {Ainf : ApartmentAtInfinity b md}
  {σ τ : SimplexAtInfinity b md}
-- given
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
  (hσ : σ ∈ Ainf.simplices)
  (hface : SimplexAtInfinity.IsFace b md τ σ) :
-- imply
  τ ∈ Ainf.simplices := by
-- proof
  apply AffineBuilding.face_in_apartment_boundary b si md Ainf hAinf σ τ hσ hface


-- created on 2026-10-23
