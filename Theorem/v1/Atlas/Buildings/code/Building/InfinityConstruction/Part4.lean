/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part2
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
