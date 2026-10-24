/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Infinity

set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- $\sigma$ is a face of $\tau$ in $X_\infty$ iff $\sigma.\text{points} \subseteq \tau.\text{points}$. -/
def SimplexAtInfinity.IsFace (b : Building V) (md : ApartmentMetricData b)
    (σ τ : SimplexAtInfinity b md) : Prop :=
  σ.points ⊆ τ.points

/-- Reflexivity of the face relation on simplices at infinity. -/
theorem SimplexAtInfinity.IsFace.refl (b : Building V) (md : ApartmentMetricData b)
    (σ : SimplexAtInfinity b md) :
    SimplexAtInfinity.IsFace b md σ σ :=
  Set.Subset.refl _

/-- Transitivity of the face relation. -/
theorem SimplexAtInfinity.IsFace.trans {b : Building V} {md : ApartmentMetricData b}
    {σ τ ρ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ ρ) :
    SimplexAtInfinity.IsFace b md σ ρ :=
  Set.Subset.trans h₁ h₂

/-- Antisymmetry of the face relation at the point-set level. -/
theorem SimplexAtInfinity.IsFace.antisymm_points {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ σ) :
    σ.points = τ.points :=
  Set.Subset.antisymm h₁ h₂

/-- Extensionality: simplices at infinity are equal iff their point sets coincide. -/
theorem SimplexAtInfinity.ext' {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h : σ.points = τ.points) : σ = τ := by
  cases σ; cases τ; simp only [SimplexAtInfinity.mk.injEq] at h ⊢; exact h

/-- The face poset below $\sigma$ inside a chosen set $S$ of simplices at infinity. -/
def FacePoset (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :=
  { τ : SimplexAtInfinity b md // τ ∈ S ∧ SimplexAtInfinity.IsFace b md τ σ }

/-- Partial order on `FacePoset` induced by the face relation on simplices at infinity. -/
instance FacePoset.instPartialOrder (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :
    PartialOrder (FacePoset b md S σ) where
  le τ₁ τ₂ := SimplexAtInfinity.IsFace b md τ₁.val τ₂.val
  le_refl τ := SimplexAtInfinity.IsFace.refl b md τ.val
  le_trans _ _ _ h₁ h₂ := SimplexAtInfinity.IsFace.trans h₁ h₂
  le_antisymm τ₁ τ₂ h₁ h₂ :=
    Subtype.ext (SimplexAtInfinity.ext' (SimplexAtInfinity.IsFace.antisymm_points h₁ h₂))

/-- $A_\infty$: the apartment at infinity built from a Euclidean apartment $A$,
consisting of all ideal simplices arising from sectors in $A$. -/
noncomputable def apartmentBoundary (b : Building V) (_si : SectorInfrastructure b)
    (md : ApartmentMetricData b) (A : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments) : ApartmentAtInfinity b md where
  apartment := A
  apartment_mem := hA
  simplices := { σ : SimplexAtInfinity b md |
    ∃ (S : Sector b), S.apartment = A ∧ σ.points ⊆ S.pointsAtInfinity md }
  simplices_from_apartment := fun _σ ⟨S, hS_apt, _⟩ => ⟨S, hS_apt⟩

/-- The full set of ideal simplices: simplices contained in $S_\infty$ for some
sector $S$ of some apartment of $X$. -/
def allSimplicesAtInfinity (b : Building V) (_si : SectorInfrastructure b)
    (md : ApartmentMetricData b) : Set (SimplexAtInfinity b md) :=
  { σ | ∃ A ∈ b.apartmentSystem.apartments,
    ∃ (S : Sector b), S.apartment = A ∧ σ.points ⊆ S.pointsAtInfinity md }

/-- The set of apartments-at-infinity, one for each Euclidean apartment via `apartmentBoundary`. -/
def allApartmentsAtInfinity (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b) : Set (ApartmentAtInfinity b md) :=
  { Ainf | ∃ (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments),
      Ainf = apartmentBoundary b si md A hA }

/-- Every apartment-at-infinity injects into the global simplex set and is closed
under taking faces. -/
theorem apartment_simplices_sub (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
    (Ainf.simplices ⊆ allSimplicesAtInfinity b si md) ∧
    (∀ (σ τ : SimplexAtInfinity b md),
      σ ∈ Ainf.simplices → SimplexAtInfinity.IsFace b md τ σ → τ ∈ Ainf.simplices) := by
  constructor
  ·
    intro σ hσ
    obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
    subst hAinf_eq
    simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
    obtain ⟨S, hS_apt, hS_pts⟩ := hσ
    exact ⟨A, hA_mem, S, hS_apt, hS_pts⟩
  ·
    intro σ τ hσ hface
    obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
    subst hAinf_eq
    simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
    obtain ⟨S, hS_apt, hS_pts⟩ := hσ
    exact ⟨S, hS_apt, Set.Subset.trans hface hS_pts⟩

/-- A subset of simplices at infinity is a *simplicial subcomplex* of $X_\infty$: it
is contained in the building's simplex set and closed under taking faces. -/
structure BuildingAtInfinity.IsSimplicialSubcomplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md)
    (sub : Set (SimplexAtInfinity b md)) : Prop where
  subset : sub ⊆ Binf.simplices
  face_closed : ∀ (σ τ : SimplexAtInfinity b md),
    σ ∈ sub → SimplexAtInfinity.IsFace b md τ σ → τ ∈ sub

/-- **Any two ideal simplices lie in a common apartment-at-infinity** — the building
axiom (BU1) for $X_\infty$ (Section 16.9). -/
theorem any_two_simplices_common_apartment (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (σ₁ : SimplexAtInfinity b md) (hσ₁ : σ₁ ∈ allSimplicesAtInfinity b si md)
    (σ₂ : SimplexAtInfinity b md) (hσ₂ : σ₂ ∈ allSimplicesAtInfinity b si md) :
    ∃ Ainf ∈ allApartmentsAtInfinity b si md,
      σ₁ ∈ Ainf.simplices ∧ σ₂ ∈ Ainf.simplices := by

  obtain ⟨A₁, hA₁, S₁, hS₁_apt, hS₁_pts⟩ := hσ₁
  obtain ⟨A₂, hA₂, S₂, hS₂_apt, hS₂_pts⟩ := hσ₂

  obtain ⟨A, hA_mem, hS₁_in_A, hS₂_in_A⟩ :=
    si.sectors_any_common_apartment S₁ S₂

  let S₁' : Sector b := {
    apartment := A
    apartment_mem := hA_mem
    baseVertex := S₁.baseVertex
    baseVertex_mem := hS₁_in_A S₁.baseVertex S₁.baseVertex_in_sector
    vertices := S₁.vertices
    vertices_in_apartment := fun v hv => hS₁_in_A v hv
    baseVertex_in_sector := S₁.baseVertex_in_sector
    nonempty := S₁.nonempty
  }
  let S₂' : Sector b := {
    apartment := A
    apartment_mem := hA_mem
    baseVertex := S₂.baseVertex
    baseVertex_mem := hS₂_in_A S₂.baseVertex S₂.baseVertex_in_sector
    vertices := S₂.vertices
    vertices_in_apartment := fun v hv => hS₂_in_A v hv
    baseVertex_in_sector := S₂.baseVertex_in_sector
    nonempty := S₂.nonempty
  }

  refine ⟨apartmentBoundary b si md A hA_mem,
    ⟨A, hA_mem, rfl⟩, ?_, ?_⟩
  ·
    show ∃ S : Sector b, S.apartment = A ∧ σ₁.points ⊆ Sector.pointsAtInfinity S md
    refine ⟨S₁', rfl, ?_⟩
    intro p hp
    obtain ⟨ρ, hρ_in, hρ_eq⟩ := hS₁_pts hp
    exact ⟨ρ, hρ_in, hρ_eq⟩
  ·
    show ∃ S : Sector b, S.apartment = A ∧ σ₂.points ⊆ Sector.pointsAtInfinity S md
    refine ⟨S₂', rfl, ?_⟩
    intro p hp
    obtain ⟨ρ, hρ_in, hρ_eq⟩ := hS₂_pts hp
    exact ⟨ρ, hρ_in, hρ_eq⟩

/-- Constructs the building at infinity $X_\infty$ as a `BuildingAtInfinity`, using
all ideal simplices and all apartment boundaries. -/
noncomputable def buildBoundaryComplex (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b) :
    BuildingAtInfinity b md where
  simplices := allSimplicesAtInfinity b si md
  apartments := allApartmentsAtInfinity b si md
  apartment_simplices_mem := fun Ainf hAinf =>
    (apartment_simplices_sub b si md Ainf hAinf).1
  contains_pair := fun σ₁ hσ₁ σ₂ hσ₂ =>
    any_two_simplices_common_apartment b si md σ₁ hσ₁ σ₂ hσ₂

/-- Sectors with the same direction have the same set of points at infinity. -/
def ApartmentBoundary_face_lattice_is_powerset (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) : Prop :=
  ∀ (Ainf : ApartmentAtInfinity b md),
    Ainf ∈ allApartmentsAtInfinity b si md →
    ∀ (σ : SimplexAtInfinity b md), σ ∈ Ainf.simplices →
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md Ainf.simplices σ)) (Finset (Fin n)))

/-- Every simplex in an apartment-at-infinity has a finite point set. -/
noncomputable def withBotNonemptyEquivFinset (n : ℕ) :
    WithBot { s : Finset (Fin n) // s.Nonempty } ≃o Finset (Fin n) where
  toFun := fun x => match x with
    | none => ∅
    | some ⟨s, _⟩ => s
  invFun := fun s => if h : s.Nonempty then some ⟨s, h⟩ else none
  left_inv := by
    rintro (_ | ⟨s, hs⟩)
    · simp only [dite_eq_right_iff]
      intro h; exact absurd h Finset.not_nonempty_empty
    · simp [hs]
  right_inv := by
    intro s
    by_cases h : s.Nonempty
    · simp [h]
    · rw [Finset.not_nonempty_iff_eq_empty] at h; simp [h]
  map_rel_iff' := by
    rintro (a | ⟨a, ha⟩) (b | ⟨b, hb⟩)
    · simp
    · exact ⟨fun _ => bot_le, fun _ => Finset.empty_subset _⟩
    · constructor
      · intro h
        change a ⊆ ∅ at h
        exact absurd (Finset.subset_empty.mp h ▸ ha) Finset.not_nonempty_empty
      · intro h; exact absurd h (WithBot.not_coe_le_bot _)
    · exact Iff.symm WithBot.coe_le_coe

/-- The face poset below $\sigma$ in $A_\infty$ is order-isomorphic to a finite powerset. -/
def ApartmentBoundary_glb_in_apartment (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) : Prop :=
  ∀ (Ainf : ApartmentAtInfinity b md),
    Ainf ∈ allApartmentsAtInfinity b si md →
    ∀ (σ₁ σ₂ : SimplexAtInfinity b md),
      σ₁ ∈ Ainf.simplices → σ₂ ∈ Ainf.simplices →
      ∃ (γ : SimplexAtInfinity b md), γ ∈ Ainf.simplices ∧
        SimplexAtInfinity.IsFace b md γ σ₁ ∧
        SimplexAtInfinity.IsFace b md γ σ₂ ∧
        (∀ (δ : SimplexAtInfinity b md), δ ∈ Ainf.simplices →
          SimplexAtInfinity.IsFace b md δ σ₁ →
          SimplexAtInfinity.IsFace b md δ σ₂ →
          SimplexAtInfinity.IsFace b md δ γ)

/-- Apartments-at-infinity admit greatest lower bounds for pairs of simplices. -/
structure BuildingAtInfinity.IsSimplicialComplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md) : Prop where
  face_lattice_powerset :
    ∀ (σ : SimplexAtInfinity b md), σ ∈ Binf.simplices →
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md Binf.simplices σ)) (Finset (Fin n)))
  glb_exists :
    ∀ (σ₁ σ₂ : SimplexAtInfinity b md),
      σ₁ ∈ Binf.simplices → σ₂ ∈ Binf.simplices →
      ∃ (γ : SimplexAtInfinity b md), γ ∈ Binf.simplices ∧
        SimplexAtInfinity.IsFace b md γ σ₁ ∧
        SimplexAtInfinity.IsFace b md γ σ₂ ∧
        (∀ (δ : SimplexAtInfinity b md), δ ∈ Binf.simplices →
          SimplexAtInfinity.IsFace b md δ σ₁ →
          SimplexAtInfinity.IsFace b md δ σ₂ →
          SimplexAtInfinity.IsFace b md δ γ)

/-- A face of a simplex of $A_\infty$ is itself a simplex of $A_\infty$. -/
theorem face_in_apartment_boundary (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md) (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ τ : SimplexAtInfinity b md)
    (hσ : σ ∈ Ainf.simplices)
    (hface : SimplexAtInfinity.IsFace b md τ σ) :
    τ ∈ Ainf.simplices := by
  obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
  subst hAinf_eq
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ
  exact ⟨S, hS_apt, Set.Subset.trans hface hS_pts⟩

/-- Order isomorphism: the face poset of $\sigma$ in $X_\infty$ agrees with the
face poset in any apartment $A_\infty$ containing $\sigma$. -/
noncomputable def facePosetIsoOfApartment (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md) (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ : SimplexAtInfinity b md) (hσ : σ ∈ Ainf.simplices) :
    OrderIso (FacePoset b md (allSimplicesAtInfinity b si md) σ)
             (FacePoset b md Ainf.simplices σ) where
  toFun := fun ⟨τ, hτ_bldg, hface⟩ =>
    ⟨τ, face_in_apartment_boundary b si md Ainf hAinf σ τ hσ hface, hface⟩
  invFun := fun ⟨τ, hτ_apt, hface⟩ =>
    ⟨τ, (apartment_simplices_sub b si md Ainf hAinf).1 hτ_apt, hface⟩
  left_inv := fun ⟨τ, _, _⟩ => by simp
  right_inv := fun ⟨τ, _, _⟩ => by simp
  map_rel_iff' := by
    intro ⟨τ₁, _, _⟩ ⟨τ₂, _, _⟩
    simp only [Equiv.coe_fn_mk]
    rfl

/-- Axiom SC1 for $X_\infty$: the face lattice below every simplex is a powerset. -/
structure SphericalSimplicialComplex (b : Building V) (md : ApartmentMetricData b) where
  building : BuildingAtInfinity b md
  spherical : building.IsSpherical b md
  simplicialComplex : building.IsSimplicialComplex

/-- Bundled constructor: produces a `SphericalSimplicialComplex` from $X$, $si$, and $md$. -/
end AffineBuilding
