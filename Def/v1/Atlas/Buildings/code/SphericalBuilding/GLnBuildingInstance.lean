/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnBuildingInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnInstance
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnThinApartmentUnconditional
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnApartmentIsoUnconditional.Part2
import Lemma.Nat.InjectiveJoinSub
import Lemma.List.Lt.of.Lt.Lt_Length.Lt_Length.IsChainLt
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnCommonApartmentUnconditional.Part3


namespace GLnBuilding

/-- Main theorem: the flag complex of $\mathrm{GL}_n(k)$ over any field $k$ is a building,
constructed unconditionally by combining the thinness, common-apartment, and apartment-iso
proofs. -/
noncomputable def glnIsBuilding_unconditional (k : Type*) [Field k] (n : ℕ) : IsBuilding k n :=
  glnIsBuilding k n
    (thinApartmentHypUnconditional k n)
    (commonApartmentHypUnconditional k n)
    (apartmentIsoHypUnconditional k n)

end GLnBuilding
