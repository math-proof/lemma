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
import Def.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery.Part2
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- Hypotheses for the prescribed-gallery construction: existence of an apartment chain of any
prescribed length, and the lift of apartment adjacency to building adjacency. -/
structure PrescribedGalleryHypotheses (b : Building V) where
  apt_gallery_of_type :
    ∀ A ∈ b.apartmentSystem.apartments,
    ∀ (C : Finset V), C ∈ A.faces → A.IsMaximal C →
    ∀ (τ : List (Finset V)),
    ∃ (cs : List (Finset V)),
      cs.head? = some C ∧
      cs.length = τ.length + 1 ∧
      (∀ E ∈ cs, E ∈ A.faces) ∧
      List.IsChain A.Adjacent cs
  apt_adj_implies_bldg_adj :
    ∀ A ∈ b.apartmentSystem.apartments,
    ∀ C D : Finset V, C ∈ A.faces → D ∈ A.faces →
      A.Adjacent C D → b.toSimplicialComplex.Adjacent C D

end CombinatorialGeometry
