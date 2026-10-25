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
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part3
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A building isometry preserves parallelism of continuous geodesic rays. -/
theorem isometry_preserves_parallelism_continuous
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ₁ ρ₂ : ContinuousGeodesicRay b md)
    (h : ContinuousGeodesicRay.Parallel b md ρ₁ ρ₂) :
    ContinuousGeodesicRay.Parallel b md
      (φ.pushforwardContinuousRay ρ₁) (φ.pushforwardContinuousRay ρ₂) := by
  obtain ⟨C, hC_pos, hC⟩ := h
  exact ⟨C, hC_pos, fun t => by
    simp only [BuildingIsometry.pushforwardContinuousRay, Function.comp]
    rw [φ.isometry]
    exact hC t⟩

end AffineBuilding
