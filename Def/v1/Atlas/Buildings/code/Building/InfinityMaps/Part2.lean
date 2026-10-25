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
import Theorem.v1.Atlas.Buildings.code.Building.InfinityMaps
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The origin $\rho(0)$ of a geodesic ray. -/
def GeodesicRay.origin {b : Building V} {md : ApartmentMetricData b}
    (ρ : GeodesicRay b md) : V :=
  ρ.toFun 0

/-- The point at infinity of a geodesic ray $\rho$, as the parallelism class of $\rho$. -/
def GeodesicRay.pointAtInfinity {b : Building V} {md : ApartmentMetricData b}
    (ρ : GeodesicRay b md) : PointAtInfinity b md :=
  Quot.mk (GeodesicRay.Parallel b md) ρ

end AffineBuilding
