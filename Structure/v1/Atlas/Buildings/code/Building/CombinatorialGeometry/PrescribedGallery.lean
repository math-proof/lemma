/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PrescribedGallery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Def.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
public section

open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- Three characterizing properties of an apartment: being a subcomplex, being thin, and the
property that minimal galleries starting in $A$ stay in $A$. -/
structure ApartmentCharacterization (b : Building V) (A : SimplicialComplex V) : Prop where
  sub : IsSubcomplex A b.toSimplicialComplex
  thin : ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin
  minimalStaysIn : ∀ (g : Gallery b.toSimplicialComplex) (C D : Finset V),
    MinimalGallery b.toSimplicialComplex g C D →
    C ∈ A.faces → A.IsMaximal C →
    ∀ E ∈ g.chambers, E ∈ A.faces

end CombinatorialGeometry
