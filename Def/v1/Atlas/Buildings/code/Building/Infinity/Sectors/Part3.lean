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
import Structure.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Convenience constructor for `SectorInfrastructure` using the building-level
chamber extension lemma. -/
def SectorInfrastructure.mk' (b : Building V)
    (sector_chamber_closed :
      ∀ (S : Sector b) (D : Finset V),
        D ∈ S.apartment.faces → S.apartment.IsMaximal D →
        (∃ v ∈ D, v ∈ S.vertices) → ∀ w ∈ D, w ∈ S.vertices) :
    SectorInfrastructure b :=
  { apt_face_extends_to_chamber := apt_face_extends_to_chamber_of_building b
    sector_chamber_closed := sector_chamber_closed }

end AffineBuilding
