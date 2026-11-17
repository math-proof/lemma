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
public import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part6
public section

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
