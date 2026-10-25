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
import Def.v1.Atlas.Buildings.code.Building.MaximalApartments
variable {V : Type} [DecidableEq V]


/-- The bundled maximal apartment system of a building, together with the
fact that it contains every apartment system. -/
structure Building.MaximalApartmentSystem (b : Building V) where
  system : ApartmentSystem b.toChamberComplex
  contains_all : ∀ 𝒜' : ApartmentSystem b.toChamberComplex,
    𝒜'.apartments ⊆ system.apartments
  unique : ∀ 𝒜' : ApartmentSystem b.toChamberComplex,
    (∀ 𝒜'' : ApartmentSystem b.toChamberComplex, 𝒜''.apartments ⊆ 𝒜'.apartments) →
    system.apartments = 𝒜'.apartments

