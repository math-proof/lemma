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
import Structure.v1.Atlas.Buildings.code.Building.InfinityMaps.Part2
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Two continuous geodesic rays are parallel iff they stay within a uniform
distance $C \geq 0$ of each other at all times $t \geq 0$. -/
def ContinuousGeodesicRay.Parallel (b : Building V) (md : ApartmentMetricData b)
    (ρ₁ ρ₂ : ContinuousGeodesicRay b md) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : NNReal,
    buildingDist b md (ρ₁.toFun t) (ρ₂.toFun t) ≤ C

/-- Points at infinity in the continuous parametrisation: parallelism classes
of continuous geodesic rays. -/
def ContinuousPointAtInfinity (b : Building V) (md : ApartmentMetricData b) :=
  Quot (ContinuousGeodesicRay.Parallel b md)

/-- Pushforward of a continuous geodesic ray under a building isometry. -/
noncomputable def BuildingIsometry.pushforwardContinuousRay
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md) (ρ : ContinuousGeodesicRay b md) :
    ContinuousGeodesicRay b md where
  toFun := φ.toFun ∘ ρ.toFun
  isometry := fun s t => by
    simp only [Function.comp]
    rw [φ.isometry]
    exact ρ.isometry s t

end AffineBuilding
