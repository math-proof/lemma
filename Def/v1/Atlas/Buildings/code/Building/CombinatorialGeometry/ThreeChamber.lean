/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/ThreeChamber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.PrescribedGallery.Part2
import Lemma.Finset.AdjacentToSimplicialComplex.of.Adjacent.In_Faces.In_Faces.In_Apartments
import Lemma.Finset.GalleryDistToSimplicialComplexToChamberComplex.eq.LengthToCoxeterSystemCoxeterMatrix_Delta
import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

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

end CombinatorialGeometry
