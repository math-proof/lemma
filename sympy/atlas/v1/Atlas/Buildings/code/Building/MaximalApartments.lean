/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.Basic
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Bijective.Any_And_In_Faces.is.Image.in.FacesAndEqImage.of.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments.In_Apartments
import Lemma.Finset.EqImageRefl.of.Ne.EqImageToFun.EqImageToFun.IsMaximalToSimplicialComplex
import sympy.atlas.v1.Atlas.Buildings.code.Building.Labels
import sympy.atlas.v1.Atlas.Buildings.code.Building.Spherical
import sympy.atlas.v1.Atlas.Buildings.code.Building.UniqueRetraction
import sympy.atlas.v1.Atlas.Buildings.code.Building.VertexActionHelper
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

/-- The bundled maximal apartment system of a building, together with the
fact that it contains every apartment system. -/
structure Building.MaximalApartmentSystem (b : Building V) where
  system : ApartmentSystem b.toChamberComplex
  contains_all : ∀ 𝒜' : ApartmentSystem b.toChamberComplex,
    𝒜'.apartments ⊆ system.apartments
  unique : ∀ 𝒜' : ApartmentSystem b.toChamberComplex,
    (∀ 𝒜'' : ApartmentSystem b.toChamberComplex, 𝒜''.apartments ⊆ 𝒜'.apartments) →
    system.apartments = 𝒜'.apartments

/-- The diameter of the link of a simplex $x$ inside the complex $K$. -/
noncomputable def SimplicialComplex.linkDiameter
    (K : SimplicialComplex V) (F : Finset V) (hF : F ∈ K.faces) : ℕ :=
  sSup { n | ∃ C D : Finset V,
    C ∈ K.link F hF ∧ D ∈ K.link F hF ∧

    (∀ C' ∈ K.link F hF, C ⊆ C' → C = C') ∧

    (∀ D' ∈ K.link F hF, D ⊆ D' → D = D') ∧
    galleryDist K (F ∪ C) (F ∪ D) = n }

/-- The Coxeter data attached to a building, extracted from the diameters of
its links. -/
def Building.CoxeterDataFromLinks
    {B : Type*} [DecidableEq B] [Fintype B]
    (b : Building V)
    (M : CoxeterMatrix B)
    (lab : Labelling b.toChamberComplex.toSimplicialComplex B)
    (C : Finset V)
    (_hC : b.toChamberComplex.toSimplicialComplex.IsMaximal C) : Prop :=
  ∀ s t : B, s ≠ t →
    ∃ F : Finset V,
      ∃ hF : F ∈ b.toChamberComplex.toSimplicialComplex.faces,

        F ⊆ C ∧

        lab.labelMap F = Finset.univ \ {s, t} ∧

        M.M s t = b.toChamberComplex.toSimplicialComplex.linkDiameter F hF
