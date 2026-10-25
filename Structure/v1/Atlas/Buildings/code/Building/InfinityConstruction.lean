/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.Building.Infinity
import Theorem.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part2
set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A subset of simplices at infinity is a *simplicial subcomplex* of $X_\infty$: it
is contained in the building's simplex set and closed under taking faces. -/
structure BuildingAtInfinity.IsSimplicialSubcomplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md)
    (sub : Set (SimplexAtInfinity b md)) : Prop where
  subset : sub ⊆ Binf.simplices
  face_closed : ∀ (σ τ : SimplexAtInfinity b md),
    σ ∈ sub → SimplexAtInfinity.IsFace b md τ σ → τ ∈ sub

end AffineBuilding
