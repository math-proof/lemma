/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptThinness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
open ChamberComplex

variable {V : Type*} [DecidableEq V]


namespace AptIsCoxeterProof

/-- Every face of an apartment $A$ is contained in some maximal chamber of $A$. -/
theorem apt_face_in_chamber {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (s : Finset V) (hs : s ∈ A.faces) :
    ∃ C, A.IsMaximal C ∧ s ⊆ C := by
  obtain ⟨cc, hcc_eq, _⟩ := pre.apt_thin_cc A hA
  have hs' : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
  obtain ⟨C, hCmax, hsC⟩ := cc.exists_maximal s hs'
  exact ⟨C, hcc_eq ▸ hCmax, hsC⟩

/-- Any two maximal chambers of an apartment $A$ are connected by a gallery internal to $A$. -/
theorem apt_gallery_connected {K : ChamberComplex V} (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments)
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    ∃ g : Gallery A, g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by
  obtain ⟨cc, hcc_eq, _⟩ := pre.apt_thin_cc A hA
  subst hcc_eq
  exact cc.gallery_connected C D hC hD

end AptIsCoxeterProof
