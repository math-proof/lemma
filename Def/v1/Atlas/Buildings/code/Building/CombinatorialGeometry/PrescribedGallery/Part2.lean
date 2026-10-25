/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PrescribedGallery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.List.Any.of.Not.In_A.IsChainA
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Lemma.Nat.NotChamberAdjacent
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.Convexity
import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes
import Def.v1.Atlas.Buildings.code.Building.RetractionDef
import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- $K$ has *prescribed gallery existence* if every chamber and label-type sequence can be realized
as the gallery-type of some gallery starting at that chamber. -/
def PrescribedGalleryExistence {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L) : Prop :=
  ∀ (C : Finset V) (τ : List (Finset L)),
    K.toSimplicialComplex.IsMaximal C →
    ∃ (g : Gallery K.toSimplicialComplex),
      g.chambers.head? = some C ∧
      GalleryType K lab g = τ

end CombinatorialGeometry
