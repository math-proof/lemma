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
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- A gallery $g$ is *minimal* between $C$ and $D$ if it connects them with length equal to the
gallery distance $d(C, D)$. -/
def MinimalGallery (K : SimplicialComplex V) (g : Gallery K)
    (C D : Finset V) : Prop :=
  g.Connects C D ∧ g.length = galleryDist K C D

/-- A gallery is *reduced* if it is non-stuttering and minimal. -/
def ReducedGallery (K : SimplicialComplex V) (g : Gallery K)
    (C D : Finset V) : Prop :=
  g.IsNonStuttering ∧ MinimalGallery K g C D

/-- The label-type of a building gallery $g$ under a labelling $\mathrm{lab}$. -/
def BuildingGalleryType {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (g : Gallery K.toSimplicialComplex) : List (Finset L) :=
  GalleryType K lab g

/-- Weyl distance $\delta_W(C, D) = (\varphi C)^{-1} \varphi D$ between chambers $C, D$ via a
Coxeter-group labelling $\varphi$. -/
noncomputable def WeylDistance {B_idx : Type*} [DecidableEq B_idx] [Fintype B_idx]
    (b : Building V) (ct : Building.CoxeterTypeOfBuilding b)
    (A : SimplicialComplex V) (_hA : A ∈ b.apartmentSystem.apartments)
    (φ : Finset V → ct.matrix.Group)
    (C D : Finset V) : ct.matrix.Group :=
  (φ C)⁻¹ * φ D

end CombinatorialGeometry
