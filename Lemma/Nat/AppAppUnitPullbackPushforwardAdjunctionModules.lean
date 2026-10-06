import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

/--
[AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean)
-/
@[main]
private lemma main
  {X Y Z : Scheme.{u}}
  {g : Z ⟶ Y}
  {f : Y ⟶ X}
  {M : X.Modules}
  {U : X.Opens} :
-- imply
  ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
-- proof
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app, pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm


-- created on 2026-10-05
