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

end CombinatorialGeometry
