import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.Buildings.code.Building.CombinatorialGeometry.RetractionHalfApartments
import Lemma.Finset.Eq.In_H.of.GtGalleryDist
open scoped Classical


namespace CombinatorialGeometry

/--
[retraction_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CombinatorialGeometry/PropStrongIsoCombinatorial.lean)
-/
@[path]
lemma retraction_dichotomy
  [DecidableEq V]
  {b : Building V}
  {cfg : RetractionHalfApartmentConfig b} :
-- imply
  cfg.ρ cfg.D = cfg.ρ' cfg.D ∨ (cfg.ρ cfg.D = cfg.s_reflection (cfg.ρ' cfg.D) ∧ cfg.ρ cfg.D ∈ cfg.H' ∧ cfg.ρ' cfg.D ∈ cfg.H) := by
-- proof
  rcases Nat.lt_trichotomy
    (galleryDist b.toSimplicialComplex cfg.C' cfg.D)
    (galleryDist b.toSimplicialComplex cfg.C cfg.D) with hlt | heq | hgt
  ·
    exact Or.inl (retraction_case_closer b cfg hlt).1
  ·
    have h := retraction_case_equal b cfg heq
    right
    refine ⟨?_, h.1, h.2.1⟩
    have hs_eq : cfg.s_reflection (cfg.ρ cfg.D) = cfg.ρ' cfg.D := h.2.2
    rw [← hs_eq, cfg.s_invol]
  ·
    exact Or.inl (retraction_case_further b cfg hgt).1

end CombinatorialGeometry


-- created on 2026-10-23
