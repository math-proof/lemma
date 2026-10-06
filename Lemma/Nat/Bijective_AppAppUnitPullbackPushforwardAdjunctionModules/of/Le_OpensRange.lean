import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

/--
[AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange.lean)
-/
@[main]
private lemma main
  {X Y : Scheme.{u}}
  {j : Y ⟶ X} [IsOpenImmersion j]
  {N : X.Modules}
  {V : X.Opens}
-- given
  (hV : V ≤ j.opensRange) :
-- imply
  Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N).app V) := by
-- proof
  have hfac := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j) (pullbackPushforwardAdjunction j) N
  have hfac' := congrArg (fun t => Hom.app t V) hfac.symm

  have heq : j ''ᵁ j ⁻¹ᵁ V = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have h2 : (homOfLE (j.image_preimage_le V)).op = eqToHom (congrArg op heq.symm) := Subsingleton.elim _ _
  have hiso1 : IsIso (N.presheaf.map (homOfLE (j.image_preimage_le V)).op) := by
    rw [h2]
    exact ⟨N.presheaf.map (eqToHom (congrArg op heq)), by simp [eqToHom_map], by simp [eqToHom_map]⟩
  have hiso2 : IsIso ((((restrictAdjunction j).leftAdjointUniq (pullbackPushforwardAdjunction j)).hom.app N).app
      (j ⁻¹ᵁ V)) := inferInstance
  have hiso := @IsIso.comp_isIso _ _ _ _ _ _ _ hiso1 hiso2
  rw [← ConcreteCategory.isIso_iff_bijective]

  revert hiso
  refine fun hiso => ?_
  rw [hfac']
  exact hiso


-- created on 2026-10-05
