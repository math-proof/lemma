/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
import Lemma.Set.IsBoundedImage.of.IsBounded.IsSimilitude
import Lemma.Finset.AreOpposite.of.AreOpposite
import Lemma.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
import Def.v1.Atlas.Buildings.code.Building.Spherical
import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Theorem.v1.Atlas.Buildings.code.Building.Infinity.Sectors
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Auxiliary axiomatic data needed to manipulate sectors: every apartment face
extends to a chamber, and the chamber containing a sector vertex is contained
in the sector. -/
structure SectorInfrastructure (_b : Building V) where
  apt_face_extends_to_chamber :
    ∀ (A : SimplicialComplex V), A ∈ _b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D
  sector_chamber_closed :
    ∀ (S : Sector _b) (D : Finset V),
      D ∈ S.apartment.faces → S.apartment.IsMaximal D →
      (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices

end AffineBuilding
