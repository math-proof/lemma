/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Theorem.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
