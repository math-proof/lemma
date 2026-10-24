/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery
import Lemma.Finset.AdjacentToSimplicialComplex.of.Adjacent.In_Faces.In_Faces.In_Apartments
import Lemma.Finset.GalleryDistToSimplicialComplexToChamberComplex.eq.LengthToCoxeterSystemCoxeterMatrix_Delta

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- Configuration of three chambers $C, D, E$ in a building, with apartments through each pair. -/
structure ThreeChamberConfig (b : Building V) where
  C : Finset V
  D : Finset V
  E : Finset V
  hC : b.toSimplicialComplex.IsMaximal C
  hD : b.toSimplicialComplex.IsMaximal D
  hE : b.toSimplicialComplex.IsMaximal E
  apt_CD : SimplicialComplex V
  apt_CD_mem : apt_CD ∈ b.apartmentSystem.apartments
  hC_CD : C ∈ apt_CD.faces
  hD_CD : D ∈ apt_CD.faces
  apt_CE : SimplicialComplex V
  apt_CE_mem : apt_CE ∈ b.apartmentSystem.apartments
  hC_CE : C ∈ apt_CE.faces
  hE_CE : E ∈ apt_CE.faces
  apt_DE : SimplicialComplex V
  apt_DE_mem : apt_DE ∈ b.apartmentSystem.apartments
  hD_DE : D ∈ apt_DE.faces
  hE_DE : E ∈ apt_DE.faces

/-- Triangle inequality for gallery distance: $d(C, E) \le d(C, D) + d(D, E)$. -/
def ThreeChamberConfig.TriangleInequality {b : Building V}
    (cfg : ThreeChamberConfig b) : Prop :=
  galleryDist b.toSimplicialComplex cfg.C cfg.E ≤
    galleryDist b.toSimplicialComplex cfg.C cfg.D +
    galleryDist b.toSimplicialComplex cfg.D cfg.E

/-- Three chambers $C, D, E$ are *collinear* if $d(C, E) = d(C, D) + d(D, E)$ (i.e. $D$ lies on a
minimal gallery from $C$ to $E$). -/
def ThreeChamberConfig.IsCollinear {b : Building V}
    (cfg : ThreeChamberConfig b) : Prop :=
  galleryDist b.toSimplicialComplex cfg.C cfg.E =
    galleryDist b.toSimplicialComplex cfg.C cfg.D +
    galleryDist b.toSimplicialComplex cfg.D cfg.E

/-- A *strong isometry* between subsets of chambers $S_1, S_2$ is a map preserving the Weyl-valued
distance $\delta_W$. -/
def StrongIsometry {b : Building V} (δW : Building.WValuedDist b)
    (S₁ S₂ : Set (Finset V))
    (φ : Finset V → Finset V) : Prop :=
  IsStrongIsometry δW S₁ S₂ φ

/-- $S$ *lies in an apartment* if there is some apartment $A$ of the building whose face set contains $S$. -/
def SubsetInApartment (b : Building V)
    (S : Set (Finset V)) : Prop :=
  ∃ A ∈ b.apartmentSystem.apartments, ∀ C ∈ S, C ∈ A.faces

/-- Hypotheses underlying the three-chamber argument: concatenability of galleries and existence of
a minimal gallery between any two maximal chambers. -/
structure ThreeChamberHypotheses (b : Building V) where
  gallery_concat :
    ∀ (C₁ C₂ C₃ : Finset V)
      (g₁ g₂ : Gallery b.toSimplicialComplex),
      g₁.Connects C₁ C₂ → g₂.Connects C₂ C₃ →
      ∃ g₃ : Gallery b.toSimplicialComplex,
        g₃.Connects C₁ C₃ ∧
        g₃.length = g₁.length + g₂.length ∧
        C₂ ∈ g₃.chambers
  minimal_gallery_exists :
    ∀ (C D : Finset V),
      b.toSimplicialComplex.IsMaximal C →
      b.toSimplicialComplex.IsMaximal D →
      ∃ g : Gallery b.toSimplicialComplex,
        g.Connects C D ∧ g.length = galleryDist b.toSimplicialComplex C D
