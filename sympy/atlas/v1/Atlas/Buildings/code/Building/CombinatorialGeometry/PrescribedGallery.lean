/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PrescribedGallery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.List.Any.of.Not.In_A.IsChainA
import Lemma.Finset.IsMaximalToSimplicialComplex.of.IsMaximal.In_Apartments
import Lemma.Nat.NotChamberAdjacent
import sympy.atlas.v1.Atlas.Buildings.code.Building.Labels
import sympy.atlas.v1.Atlas.Buildings.code.Building.Convexity
import sympy.atlas.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import sympy.atlas.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes
import sympy.atlas.v1.Atlas.Buildings.code.Building.RetractionDef

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

/-- Three characterizing properties of an apartment: being a subcomplex, being thin, and the
property that minimal galleries starting in $A$ stay in $A$. -/
structure ApartmentCharacterization (b : Building V) (A : SimplicialComplex V) : Prop where
  sub : IsSubcomplex A b.toSimplicialComplex
  thin : ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin
  minimalStaysIn : ∀ (g : Gallery b.toSimplicialComplex) (C D : Finset V),
    MinimalGallery b.toSimplicialComplex g C D →
    C ∈ A.faces → A.IsMaximal C →
    ∀ E ∈ g.chambers, E ∈ A.faces

/-- $K$ has *prescribed gallery existence* if every chamber and label-type sequence can be realized
as the gallery-type of some gallery starting at that chamber. -/
def PrescribedGalleryExistence {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L) : Prop :=
  ∀ (C : Finset V) (τ : List (Finset L)),
    K.toSimplicialComplex.IsMaximal C →
    ∃ (g : Gallery K.toSimplicialComplex),
      g.chambers.head? = some C ∧
      GalleryType K lab g = τ

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
