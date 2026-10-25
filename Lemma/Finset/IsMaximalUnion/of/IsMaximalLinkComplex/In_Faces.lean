import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.LinkBuildingIsoHelper
open SimplicialComplex in


/--
[union_maximal_of_linkComplex_maximal_helper](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkBuildingIsoHelper.lean)
-/
@[path]
private lemma union_maximal_of_linkComplex_maximal_helper_eq
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ_max : (K.linkComplex σ hσ).IsMaximal τ) :
-- imply
  K.IsMaximal (σ ∪ τ) := by
-- proof
  apply union_maximal_of_linkComplex_maximal_helper hσ hτ_max

private lemma apt_automorphism_sending_chamber'_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  apply apt_automorphism_sending_chamber' b A hA C hC D hD

private lemma finset_image_ssubset_of_injective'_eq
  {V : Type}
  [DecidableEq V]
  {f : V → V}
  {s t : Finset V}
-- given
  (hf : Function.Injective f)
  (h : s ⊂ t) :
-- imply
  s.image f ⊂ t.image f := by
-- proof
  apply finset_image_ssubset_of_injective' hf h

private lemma bijective_face_iso_preserves_maximal'_eq
  {V : Type}
  [DecidableEq V]
  {A A' : SimplicialComplex V}
  {φ : V → V}
  {s : Finset V}
-- given
  (hφ_bij : Function.Bijective φ)
  (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
  (hs : A.IsMaximal s) :
-- imply
  A'.IsMaximal (s.image φ) := by
-- proof
  apply bijective_face_iso_preserves_maximal' hφ_bij hφ_faces hs

private lemma iso_bijective_fixing_chamber'_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {B : SimplicialComplex V}
  {B₀ : SimplicialComplex V}
  {D : Finset V}
-- given
  (hB : B ∈ b.apartmentSystem.apartments)
  (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
  (hD_B : D ∈ B.faces)
  (hD_B₀ : D ∈ B₀.faces)
  (hD_max_B : B.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧ D.image φ = D := by
-- proof
  apply iso_bijective_fixing_chamber' b B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B

private lemma bij_iso_fixing_chamber_is_id'_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {B B' : SimplicialComplex V}
  {D : Finset V}
  {φ : V → V}
-- given
  (hB : B ∈ b.apartmentSystem.apartments)
  (hD_B : D ∈ B.faces)
  (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D)
  (hφ_bij : Function.Bijective φ)
  (hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
  (hφ_D : D.image φ = D) :
-- imply
  ∀ s ∈ B.faces, s.image φ = s := by
-- proof
  apply bij_iso_fixing_chamber_is_id' b B B' hB D hD_B hD_max φ hφ_bij hφ_faces hφ_D


-- created on 2026-10-24
