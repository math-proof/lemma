/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Def.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
