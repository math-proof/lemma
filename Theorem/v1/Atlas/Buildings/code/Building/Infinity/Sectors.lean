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
import Def.v1.Atlas.Buildings.code.Building.Infinity.Sectors.Part2
set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- Every face of an apartment extends to a maximal face (chamber) of that apartment. -/
theorem apt_face_extends_to_chamber_of_building (b : Building V) :
    ∀ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments →
      ∀ s ∈ A.faces, ∃ D ∈ A.faces, A.IsMaximal D ∧ s ⊆ D := by
  intro A hA_mem s hs_face

  obtain ⟨_B_idx, _M, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA_mem


  have hs_cc : s ∈ cc.faces := hcc_eq ▸ hs_face
  obtain ⟨C, hC_max, hs_sub_C⟩ := cc.exists_maximal s hs_cc

  have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max
  exact ⟨C, hC_max_A.1, hC_max_A, hs_sub_C⟩

end AffineBuilding
