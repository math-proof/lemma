/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryBuildingWiring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryCommonApartment
import Def.v1.Atlas.Buildings.code.SphericalBuilding.IsometryApartmentExchange
import Lemma.Set.Simplices.of.In_StandardApartments.In_StandardApartments


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Concrete wiring: produces the isometry building from a hyperbolic frame, by plugging in
the common-apartment and apartment-exchange instances. -/
noncomputable def isometryIsBuilding_wired
    (B : LinearMap.BilinForm k V) (n : ℕ)
    (frame : HyperbolicFrame B n) :
    IsBuilding B n :=
  isometryIsBuilding B n
    (commonIsotropicApartmentHyp B n frame)
    (apartmentExchangeHypInstance B n)

end IsometryBuilding
