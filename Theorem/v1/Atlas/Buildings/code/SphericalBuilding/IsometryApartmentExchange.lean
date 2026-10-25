/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryApartmentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance.Part2


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Helper: in the isometry building, all standard apartments share the same set of simplices
(namely, all isotropic chains). -/
theorem standardApartments_simplices_eq (B : LinearMap.BilinForm k V) (n : ℕ)
    (A₁ : Apartment B n) (hA₁ : A₁ ∈ standardApartments B n)
    (A₂ : Apartment B n) (hA₂ : A₂ ∈ standardApartments B n) :
    A₁.simplices = A₂.simplices := by
  obtain ⟨frame₁, rfl⟩ := hA₁
  obtain ⟨frame₂, rfl⟩ := hA₂
  rfl

end IsometryBuilding
