import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.RetractionHalfApartments
open CombinatorialGeometry
open scoped Classical


namespace CombinatorialGeometry

/--
[retraction_case_further](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/RetractionHalfApartments.lean)
-/
@[path]
lemma retraction_case_further
  [DecidableEq V]
  {b : Building V}
  {cfg : RetractionHalfApartmentConfig b}
-- given
  (hfurther : galleryDist b.toSimplicialComplex cfg.C' cfg.D > galleryDist b.toSimplicialComplex cfg.C cfg.D) :
-- imply
  cfg.ρ cfg.D = cfg.ρ' cfg.D ∧ cfg.ρ cfg.D ∈ cfg.H := by
-- proof
  have hcollinear : galleryDist b.toSimplicialComplex cfg.C' cfg.D =
    galleryDist b.toSimplicialComplex cfg.C' cfg.C +
    galleryDist b.toSimplicialComplex cfg.C cfg.D := by
    have hbound := cfg.adj_triangle
    rw [cfg.adj_dist']
    omega
  have hyp := threeChamberHypotheses_of_building b
  have hcommon := three_chambers_common_apartment b hyp cfg.C' cfg.C cfg.D cfg.hC' cfg.hC cfg.hD
    hcollinear
  have hcommon' : ∃ B ∈ b.apartmentSystem.apartments,
    cfg.C ∈ B.faces ∧ cfg.C' ∈ B.faces ∧ cfg.D ∈ B.faces := by
    obtain ⟨B, hB, hC'B, hCB, hDB⟩ := hcommon
    exact ⟨B, hB, hCB, hC'B, hDB⟩
  constructor
  ·
    exact cfg.retraction_agree_on_common_apt hcommon'
  ·
    have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    have hdist_C : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) =
      galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ_preserves_dist_C cfg.D cfg.hD
    rw [cfg.H_char (cfg.ρ cfg.D) hρD_face hρD_max, hdist_C]
    have hρ_eq := cfg.retraction_agree_on_common_apt hcommon'
    rwa [hρ_eq, cfg.ρ'_preserves_dist_C' cfg.D cfg.hD]

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[retraction_case_closer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/RetractionHalfApartments.lean)
-/
@[path]
lemma retraction_case_closer
  [DecidableEq V]
  {b : Building V}
  {cfg : RetractionHalfApartmentConfig b}
-- given
  (hcloser : galleryDist b.toSimplicialComplex cfg.C' cfg.D < galleryDist b.toSimplicialComplex cfg.C cfg.D) :
-- imply
  cfg.ρ cfg.D = cfg.ρ' cfg.D ∧ cfg.ρ cfg.D ∈ cfg.H' := by
-- proof
  have hcollinear : galleryDist b.toSimplicialComplex cfg.C cfg.D =
    galleryDist b.toSimplicialComplex cfg.C cfg.C' +
    galleryDist b.toSimplicialComplex cfg.C' cfg.D := by
    have hbound := cfg.adj_triangle'
    rw [cfg.adj_dist]
    omega
  have hyp := threeChamberHypotheses_of_building b
  have hcommon := three_chambers_common_apartment b hyp cfg.C cfg.C' cfg.D cfg.hC cfg.hC' cfg.hD
    hcollinear
  have hcommon' : ∃ B ∈ b.apartmentSystem.apartments,
    cfg.C ∈ B.faces ∧ cfg.C' ∈ B.faces ∧ cfg.D ∈ B.faces := by
    obtain ⟨B, hB, hCB, hC'B, hDB⟩ := hcommon
    exact ⟨B, hB, hCB, hC'B, hDB⟩
  constructor
  · exact cfg.retraction_agree_on_common_apt hcommon'
  · have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    rw [cfg.H'_char (cfg.ρ cfg.D) hρD_face hρD_max]
    have hρ_eq := cfg.retraction_agree_on_common_apt hcommon'
    rw [hρ_eq, cfg.ρ'_preserves_dist_C' cfg.D cfg.hD,
      ← hρ_eq, cfg.ρ_preserves_dist_C cfg.D cfg.hD]
    exact hcloser

end CombinatorialGeometry

namespace CombinatorialGeometry

/--
[retraction_case_equal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/RetractionHalfApartments.lean)
-/
@[path]
lemma retraction_case_equal
  [DecidableEq V]
  {b : Building V}
  {cfg : RetractionHalfApartmentConfig b}
-- given
  (hequal : galleryDist b.toSimplicialComplex cfg.C' cfg.D = galleryDist b.toSimplicialComplex cfg.C cfg.D) :
-- imply
  cfg.ρ cfg.D ∈ cfg.H' ∧ cfg.ρ' cfg.D ∈ cfg.H ∧ cfg.s_reflection (cfg.ρ cfg.D) = cfg.ρ' cfg.D := by
-- proof
  have hρD_in_H' : cfg.ρ cfg.D ∈ cfg.H' := by
    have hρD_face := cfg.ρ_maps_to_A cfg.D cfg.hD
    have hρD_max := cfg.ρ_maximal cfg.D cfg.hD
    rw [cfg.H'_char (cfg.ρ cfg.D) hρD_face hρD_max]
    have hdist_C : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) =
      galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ_preserves_dist_C cfg.D cfg.hD
    have hdist_C'_le : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ cfg.D) ≤
      galleryDist b.toSimplicialComplex cfg.C' cfg.D :=
      cfg.ρ_diminishes_dist_C' cfg.D cfg.hD
    have h_le : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ cfg.D) ≤
      galleryDist b.toSimplicialComplex cfg.C (cfg.ρ cfg.D) := by
      rw [hdist_C, ← hequal]; exact hdist_C'_le
    have hne := cfg.coxeter_dist_ne (cfg.ρ cfg.D) hρD_face hρD_max
    exact lt_of_le_of_ne h_le hne
  have hρ'D_in_H : cfg.ρ' cfg.D ∈ cfg.H := by
    have hρ'D_face := cfg.ρ'_maps_to_A cfg.D cfg.hD
    have hρ'D_max := cfg.ρ'_maximal cfg.D cfg.hD
    rw [cfg.H_char (cfg.ρ' cfg.D) hρ'D_face hρ'D_max]
    have hdist_C' : galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) =
      galleryDist b.toSimplicialComplex cfg.C' cfg.D :=
      cfg.ρ'_preserves_dist_C' cfg.D cfg.hD
    have hdist_C_le : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≤
      galleryDist b.toSimplicialComplex cfg.C cfg.D :=
      cfg.ρ'_diminishes_dist_C cfg.D cfg.hD
    have h_le : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≤
      galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) := by
      rw [hdist_C', hequal]; exact hdist_C_le
    have hne : galleryDist b.toSimplicialComplex cfg.C (cfg.ρ' cfg.D) ≠
      galleryDist b.toSimplicialComplex cfg.C' (cfg.ρ' cfg.D) := by
      intro heq
      exact cfg.coxeter_dist_ne (cfg.ρ' cfg.D) hρ'D_face hρ'D_max heq.symm
    exact lt_of_le_of_ne h_le hne
  exact ⟨hρD_in_H', hρ'D_in_H, cfg.s_reflection_eq_of_equal_dist hequal⟩

end CombinatorialGeometry


-- created on 2026-10-23
