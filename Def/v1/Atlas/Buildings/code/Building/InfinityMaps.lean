/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
import Lemma.Set.PointsAtInfinity.of.Vertices
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Def.v1.Atlas.Buildings.code.Building.Labels
import Mathlib.Data.NNReal.Basic
import Structure.v1.Atlas.Buildings.code.Building.InfinityMaps
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The pushforward of a geodesic ray $\rho$ under a building isometry
$\varphi$ is the composite ray $\varphi \circ \rho$. -/
noncomputable def BuildingIsometry.pushforwardRay
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : GeodesicRay b md) :
    GeodesicRay b md where
  toFun := φ.toFun ∘ ρ.toFun
  isometry := fun m n => by
    simp only [Function.comp]
    rw [φ.isometry]
    exact ρ.isometry m n

end AffineBuilding
