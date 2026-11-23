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
public import Theorem.v1.Atlas.Buildings.code.Building.InfinityMaps.Part2

@[expose] public section

set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The induced map $\varphi_\infty$ on continuous points at infinity:
descended from the pushforward of rays through the parallelism quotient. -/
noncomputable def BuildingIsometry.inducedMapInfinityCont
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) :
    ContinuousPointAtInfinity b md → ContinuousPointAtInfinity b md :=
  Quot.lift
    (fun ρ => Quot.mk (ContinuousGeodesicRay.Parallel b md)
      (φ.pushforwardContinuousRay ρ))
    (fun ρ₁ ρ₂ hpar => Quot.sound
      (isometry_preserves_parallelism_continuous φ ρ₁ ρ₂ hpar))

/-- The origin $\rho(0)$ of a continuous geodesic ray. -/
def ContinuousGeodesicRay.origin {b : Building V} {md : ApartmentMetricData b}
    (ρ : ContinuousGeodesicRay b md) : V :=
  ρ.toFun 0

/-- The point at infinity of a continuous geodesic ray. -/
def ContinuousGeodesicRay.pointAtInfinity {b : Building V} {md : ApartmentMetricData b}
    (ρ : ContinuousGeodesicRay b md) : ContinuousPointAtInfinity b md :=
  Quot.mk (ContinuousGeodesicRay.Parallel b md) ρ

/-- The induced map $\varphi_\infty$ on points at infinity (discrete
parametrisation) descending from ray pushforward. -/
noncomputable def BuildingIsometry.inducedMapInfinity
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) :
    PointAtInfinity b md → PointAtInfinity b md :=
  Quot.lift
    (fun ρ => Quot.mk (GeodesicRay.Parallel b md) (φ.pushforwardRay ρ))
    (fun ρ₁ ρ₂ hpar => Quot.sound (isometry_preserves_parallelism φ ρ₁ ρ₂ hpar))

end AffineBuilding
