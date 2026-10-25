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
import Structure.v1.Atlas.Buildings.code.Building.InfinityMaps.Part3
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- $X_\infty$ admits a labelling: there exists a label type $L_\infty$
with a corresponding `InfinityLabelling`. -/
def InfinityLabelling.IsPreservedBy
    {V : Type} [DecidableEq V]
    {b : Building V} {md : ApartmentMetricData b}
    {L_inf : Type*} [DecidableEq L_inf]
    (lab : InfinityLabelling (b := b) (md := md) L_inf)
    (F : SimplexAtInfinity b md → SimplexAtInfinity b md) : Prop :=
  ∀ σ : SimplexAtInfinity b md, lab.labelMap (F σ) = lab.labelMap σ

end AffineBuilding
