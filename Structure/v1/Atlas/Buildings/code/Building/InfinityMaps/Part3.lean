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
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part6
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A labelling of $X_\infty$: a label-finset map on simplices at infinity
that is strictly monotone with respect to the face relation. -/
structure InfinityLabelling
    {V : Type} [DecidableEq V]
    {b : Building V} {md : ApartmentMetricData b}
    (L_inf : Type*) [DecidableEq L_inf] where
  labelMap : SimplexAtInfinity b md → Finset L_inf
  label_strictMono : ∀ (σ τ : SimplexAtInfinity b md),
    SimplexAtInfinity.IsFace b md σ τ → σ ≠ τ →
    labelMap σ ⊂ labelMap τ

end AffineBuilding
