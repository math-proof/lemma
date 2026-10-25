/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Def.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part5
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Axiom SC1 for $X_\infty$: the face lattice below every simplex is a powerset. -/
structure SphericalSimplicialComplex (b : Building V) (md : ApartmentMetricData b) where
  building : BuildingAtInfinity b md
  spherical : building.IsSpherical b md
  simplicialComplex : building.IsSimplicialComplex

end AffineBuilding
