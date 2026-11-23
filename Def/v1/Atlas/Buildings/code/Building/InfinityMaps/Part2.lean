/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
public import Theorem.Set.PointsAtInfinity.of.Vertices
public import Theorem.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
public import Def.v1.Atlas.Buildings.code.Building.Labels
public import Mathlib.Data.NNReal.Basic
public import Theorem.v1.Atlas.Buildings.code.Building.InfinityMaps

@[expose] public section

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
