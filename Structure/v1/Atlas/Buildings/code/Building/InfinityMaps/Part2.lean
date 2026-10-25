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
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part2
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A geodesic ray parametrised by $\mathbb{R}_{\geq 0}$ rather than $\mathbb{N}$:
a map $\rho : \mathbb{R}_{\geq 0} \to V$ that is an isometry onto its image. -/
structure ContinuousGeodesicRay (b : Building V) (md : ApartmentMetricData b) where
  toFun : NNReal → V
  isometry : ∀ s t : NNReal,
    buildingDist b md (toFun s) (toFun t) = |(s : ℝ) - (t : ℝ)|

end AffineBuilding
