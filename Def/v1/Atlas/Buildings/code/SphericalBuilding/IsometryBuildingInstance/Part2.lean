/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryBuildingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part3
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.IsometryBuildingInstance


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The isometry building: assembles `standardComplex` and `standardApartments` into an
`IsBuilding` structure, given the common-apartment and apartment-exchange hypotheses. -/
noncomputable def isometryIsBuilding
    (B : LinearMap.BilinForm k V) (n : ℕ)
    (h_common : CommonIsotropicApartmentHyp B n)
    (h_exchange : ApartmentExchangeHyp B n) :
    IsBuilding B n where
  complex := standardComplex B
  apartments := standardApartments B n
  apartment_subcomplex := by
    intro A hA


    obtain ⟨frame, rfl⟩ := hA
    intro σ hσ
    exact hσ
  common_apartment := h_common.find_common
  apartment_exchange := h_exchange.exchange

end IsometryBuilding
