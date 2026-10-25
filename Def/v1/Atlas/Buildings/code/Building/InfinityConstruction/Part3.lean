/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Instance.v1.Atlas.Buildings.code.Building.InfinityConstruction
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

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

end AffineBuilding
