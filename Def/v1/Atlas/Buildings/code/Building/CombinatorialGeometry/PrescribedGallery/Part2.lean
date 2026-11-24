module
public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
public import Theorem.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
public import Theorem.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
public import Theorem.List.Any.of.Not.In_A.IsChainA
public import Theorem.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
public import Theorem.Nat.NotChamberAdjacent
public import Def.v1.Atlas.Buildings.code.Building.Labels
public import Def.v1.Atlas.Buildings.code.Building.Convexity
public import Structure.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
public import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes
public import Def.v1.Atlas.Buildings.code.Building.RetractionDef
public import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PrescribedGallery.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
