import Mathlib
import sympy.Basic
import Def.ModularCurve_WeierstrassLevelModuliDatum
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_RigidWeierstrassData_exists_eq_act_of_mk_eq_mk.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing T] [Algebra A T]
  {R : ModularCurve.RigidWeierstrassData A}
  {x y : R.Raw T}
-- given
  (h : (Quot.mk _ x : R.Pt T) = Quot.mk _ y) :
-- imply
  ∃ C : WeierstrassCurve.VariableChange T, y = R.act C x := by
-- proof
  have hequiv : Equivalence (R.Rel (T := T)) :=
    { refl := fun a => ModularCurve.RigidWeierstrassData.Rel.refl R a
      symm := by
        rintro a b ⟨C, rfl⟩
        refine ⟨C⁻¹, ?_⟩
        rw [← R.act_mul, inv_mul_cancel, R.act_one]
      trans := fun h₁ h₂ => ModularCurve.RigidWeierstrassData.Rel.trans R h₁ h₂ }
  have h' : Relation.EqvGen (R.Rel (T := T)) x y := Quot.eqvGen_exact h
  exact (hequiv.eqvGen_iff).mp h'


-- created on 2026-10-23
