/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.EqImageRefl.of.Ne.EqImageToFun.EqImageToFun.IsMaximalToSimplicialComplex
import Def.v1.Atlas.Buildings.code.Building.Labels
import Def.v1.Atlas.Buildings.code.Building.Spherical
import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
import Theorem.v1.Atlas.Buildings.code.Building.VertexActionHelper
import Mathlib.GroupTheory.Coxeter.Basic
variable {V : Type} [DecidableEq V]


/-- A simplicial map $f : A \to A'$ between two apartments of a building is
*type- (or label-) preserving* if applying $f$ to any face leaves its labelling
unchanged. -/
def IsTypePreservingIso {L : Type*} [DecidableEq L]
    {b : Building V}
    (A A' : SimplicialComplex V)
    (_hA : A ∈ b.apartmentSystem.apartments)
    (_hA' : A' ∈ b.apartmentSystem.apartments)
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (f : SimplicialMap A A') : Prop :=
  ∀ s ∈ A.faces, lab.labelMap (s.image f.toFun) = lab.labelMap s

/-- Order on apartment systems: $\mathcal A_1 \le \mathcal A_2$ if every
apartment of $\mathcal A_1$ also belongs to $\mathcal A_2$. -/
def ApartmentSystem.le {K : ChamberComplex V}
    (𝒜₁ 𝒜₂ : ApartmentSystem K) : Prop :=
  𝒜₁.apartments ⊆ 𝒜₂.apartments

