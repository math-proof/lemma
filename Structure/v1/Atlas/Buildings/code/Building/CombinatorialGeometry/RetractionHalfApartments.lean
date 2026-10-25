/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/RetractionHalfApartments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber.Part2
import Lemma.Group.Atlas.v1.Buildings.code.Building.CombinatorialGeometry.ThreeChamber
open scoped Classical

variable {V : Type*} [DecidableEq V]


namespace CombinatorialGeometry

/-- Configuration of data needed for the half-apartment retraction analysis: two adjacent
chambers $C, C'$, a third chamber $D$, an apartment $A$ containing $C, C'$, two retractions
$\rho, \rho'$ onto $A$ centered at $C, C'$, the two half-apartments $H, H'$ on either side of the
wall, plus the wall reflection $s$. -/
structure RetractionHalfApartmentConfig (b : Building V) where
  C : Finset V
  C' : Finset V
  D : Finset V
  hC : b.toSimplicialComplex.IsMaximal C
  hC' : b.toSimplicialComplex.IsMaximal C'
  hD : b.toSimplicialComplex.IsMaximal D
  hCC' : C ≠ C'
  hCD : C ≠ D
  hC'D : C' ≠ D
  adj : b.toSimplicialComplex.Adjacent C C'
  A : SimplicialComplex V
  hA : A ∈ b.apartmentSystem.apartments
  hCA : C ∈ A.faces
  hC'A : C' ∈ A.faces
  ρ : Finset V → Finset V
  ρ' : Finset V → Finset V
  ρ_maps_to_A : ∀ E, b.toSimplicialComplex.IsMaximal E → ρ E ∈ A.faces
  ρ'_maps_to_A : ∀ E, b.toSimplicialComplex.IsMaximal E → ρ' E ∈ A.faces
  ρ_preserves_dist_C : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C (ρ E) = galleryDist b.toSimplicialComplex C E
  ρ'_preserves_dist_C' : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C' (ρ' E) = galleryDist b.toSimplicialComplex C' E
  ρ_diminishes_dist_C' : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C' (ρ E) ≤ galleryDist b.toSimplicialComplex C' E
  ρ'_diminishes_dist_C : ∀ E, b.toSimplicialComplex.IsMaximal E →
    galleryDist b.toSimplicialComplex C (ρ' E) ≤ galleryDist b.toSimplicialComplex C E
  H : Set (Finset V)
  H' : Set (Finset V)
  hC_in_H : C ∈ H
  hC'_in_H' : C' ∈ H'
  H_char : ∀ E ∈ A.faces, A.IsMaximal E →
    (E ∈ H ↔ galleryDist b.toSimplicialComplex C E < galleryDist b.toSimplicialComplex C' E)
  H'_char : ∀ E ∈ A.faces, A.IsMaximal E →
    (E ∈ H' ↔ galleryDist b.toSimplicialComplex C' E < galleryDist b.toSimplicialComplex C E)
  ρ_maximal : ∀ E, b.toSimplicialComplex.IsMaximal E → A.IsMaximal (ρ E)
  ρ'_maximal : ∀ E, b.toSimplicialComplex.IsMaximal E → A.IsMaximal (ρ' E)
  retraction_agree_on_common_apt :
    (∃ B ∈ b.apartmentSystem.apartments, C ∈ B.faces ∧ C' ∈ B.faces ∧ D ∈ B.faces) →
    ρ D = ρ' D
  adj_A : A.Adjacent C C'
  adj_dist : galleryDist b.toSimplicialComplex C C' = 1
  adj_dist' : galleryDist b.toSimplicialComplex C' C = 1
  adj_triangle : galleryDist b.toSimplicialComplex C' D ≤
    galleryDist b.toSimplicialComplex C D + 1
  adj_triangle' : galleryDist b.toSimplicialComplex C D ≤
    galleryDist b.toSimplicialComplex C' D + 1
  coxeter_dist_ne : ∀ E ∈ A.faces, A.IsMaximal E →
    galleryDist b.toSimplicialComplex C' E ≠ galleryDist b.toSimplicialComplex C E
  s_reflection : Finset V → Finset V
  s_swap_C : s_reflection C = C'
  s_swap_C' : s_reflection C' = C
  s_invol : ∀ E, s_reflection (s_reflection E) = E
  s_swaps_H : ∀ E ∈ H, s_reflection E ∈ H'
  s_reflection_eq_of_equal_dist :
    galleryDist b.toSimplicialComplex C' D = galleryDist b.toSimplicialComplex C D →
    s_reflection (ρ D) = ρ' D

end CombinatorialGeometry
