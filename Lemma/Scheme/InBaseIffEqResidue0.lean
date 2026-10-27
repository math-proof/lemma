import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_mem_asIdeal_base_iff_residue_germ_appTop_eq_zero.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} {R : (CommRingCat : Type (u + 1))} (f : X ⟶ Spec R) (y : X) (c : R) :
  -- imply
  c ∈ (f.base y).asIdeal ↔ X.residue y ((X.presheaf.germ ⊤ y trivial) (f.appTop ((Scheme.ΓSpecIso R).inv c))) = 0 := by
  -- proof
  have hf : f = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  have hy : f.base y = (Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop)) (X.toSpecΓ y) := by
    conv_lhs => rw [hf]
    rfl
  rw [hy, Spec.map_apply, Scheme.toSpecΓ_apply, Spec.map_apply, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap, Ideal.mem_comap]
  show _ ∈ IsLocalRing.maximalIdeal _ ↔ _
  rw [← IsLocalRing.residue_eq_zero_iff]
  rfl


-- created on 2026-10-20
