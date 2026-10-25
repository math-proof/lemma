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
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- A *sector* in a Euclidean apartment $A$ of a building: a base vertex together with
a nonempty vertex set inside $A$, modeling a Weyl chamber (Section 16.5). -/
structure Sector (b : Building V) where
  apartment : SimplicialComplex V
  apartment_mem : apartment ∈ b.apartmentSystem.apartments
  baseVertex : V
  baseVertex_mem : ∃ s ∈ apartment.faces, baseVertex ∈ s
  vertices : Set V
  vertices_in_apartment : ∀ v ∈ vertices, ∃ s ∈ apartment.faces, v ∈ s
  baseVertex_in_sector : baseVertex ∈ vertices
  nonempty : vertices.Nonempty

end AffineBuilding
