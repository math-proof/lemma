/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- $\sigma$ is a face of $\tau$ in $X_\infty$ iff $\sigma.\text{points} \subseteq \tau.\text{points}$. -/
def SimplexAtInfinity.IsFace (b : Building V) (md : ApartmentMetricData b)
    (σ τ : SimplexAtInfinity b md) : Prop :=
  σ.points ⊆ τ.points

end AffineBuilding
