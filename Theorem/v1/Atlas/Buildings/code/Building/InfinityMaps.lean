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
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A building isometry preserves parallelism of geodesic rays:
$\rho_1 \parallel \rho_2 \implies \varphi \rho_1 \parallel \varphi \rho_2$. -/
theorem isometry_preserves_parallelism
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ₁ ρ₂ : GeodesicRay b md)
    (h : GeodesicRay.Parallel b md ρ₁ ρ₂) :
    GeodesicRay.Parallel b md (φ.pushforwardRay ρ₁) (φ.pushforwardRay ρ₂) := by
  obtain ⟨C, hC_pos, hC⟩ := h
  exact ⟨C, hC_pos, fun n => by
    simp only [BuildingIsometry.pushforwardRay, Function.comp]
    rw [φ.isometry]
    exact hC n⟩

end AffineBuilding
