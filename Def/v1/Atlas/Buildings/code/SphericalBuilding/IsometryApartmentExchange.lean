/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryApartmentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance.Part2
import Theorem.v1.Atlas.Buildings.code.SphericalBuilding.IsometryApartmentExchange


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Apartment exchange axiom for the isometry building: any two apartments sharing a chamber
admit a bijection of simplices fixing the common ones. The identity works because all standard
apartments coincide as simplicial sets. -/
noncomputable def apartmentExchangeHypInstance (B : LinearMap.BilinForm k V) (n : ℕ) :
    ApartmentExchangeHyp B n where
  exchange := by
    intro A₁ hA₁ A₂ hA₂ C hC₁ _hC₂
    have heq := standardApartments_simplices_eq B n A₁ hA₁ A₂ hA₂
    exact ⟨id, Function.bijective_id, fun σ hσ => heq ▸ hσ, fun σ _ => rfl⟩

end IsometryBuilding
