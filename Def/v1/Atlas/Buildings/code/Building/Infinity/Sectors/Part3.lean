module
public import Def.v1.Atlas.Buildings.code.Building.AffineMetric.Part5
public import Theorem.Set.IsBoundedImage.of.IsBounded.IsSimilitude
public import Theorem.Finset.AreOpposite.of.AreOpposite
public import Theorem.Finset.ImageRetractionMap.in.Faces.of.IsMaximal.In_Faces.In_Apartments
public import Def.v1.Atlas.Buildings.code.Building.Spherical
public import Def.v1.Atlas.Buildings.code.Building.AptIsoFixesIntersection
public import Structure.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part3
set_option linter.unusedSectionVars false
open ChamberComplex


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/Sectors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
