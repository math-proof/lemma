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
import Theorem.v1.Atlas.Buildings.code.Building.InfinityMaps.Part4
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The induced simplex map at infinity associated to a simplicial
automorphism $f$. -/
noncomputable def inducedSimplexMapOfAuto
    {b : Building V} {md : ApartmentMetricData b}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (σ : SimplexAtInfinity b md) :
    SimplexAtInfinity b md :=
  (inducedSimplexMap_exists f hf σ).choose

/-- A building isometry preserves a chamber-complex labelling if the label
of each face is invariant under $\varphi$. -/
def BuildingIsometry.IsLabelPreserving
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    lab.labelMap (s.image φ.toFun) = lab.labelMap s

/-- A simplicial automorphism preserves a labelling iff every face has the
same label as its image. -/
def IsLabelPreservingAuto (b : Building V) (f : V → V)
    {L : Type*} [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) : Prop :=
  ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    lab.labelMap (s.image f) = lab.labelMap s

end AffineBuilding
