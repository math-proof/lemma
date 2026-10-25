/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Theorem.v1.Atlas.Buildings.code.Building.InfinityConstruction
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The face poset below $\sigma$ inside a chosen set $S$ of simplices at infinity. -/
def FacePoset (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :=
  { τ : SimplexAtInfinity b md // τ ∈ S ∧ SimplexAtInfinity.IsFace b md τ σ }

end AffineBuilding
