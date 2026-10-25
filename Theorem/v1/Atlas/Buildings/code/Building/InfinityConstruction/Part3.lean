/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
