import Mathlib
import sympy.Basic


/--
[WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_VariableChange_eq_one_of_smul_eq_of_u_eq_one_of_isUnit_six.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {W : WeierstrassCurve R}
  {C : WeierstrassCurve.VariableChange R}
-- given
  (h6 : IsUnit (6 : R))
  (hC : C • W = W)
  (hu : C.u = 1) :
-- imply
  C = 1 := by
-- proof
  have h23 : IsUnit ((2 : R) * 3) := by norm_num; exact h6
  have h2 : IsUnit (2 : R) := isUnit_of_mul_isUnit_left h23
  have h3 : IsUnit (3 : R) := isUnit_of_mul_isUnit_right h23
  have e1 := congrArg WeierstrassCurve.a₁ hC
  have e2 := congrArg WeierstrassCurve.a₂ hC
  have e3 := congrArg WeierstrassCurve.a₃ hC
  simp only [WeierstrassCurve.variableChange_def, hu, inv_one, Units.val_one, one_pow, one_mul] at e1 e2 e3
  have hs : C.s = 0 := by
    have h : (2 : R) * C.s = 0 := by linear_combination e1
    exact h2.mul_right_eq_zero.mp h
  have hr : C.r = 0 := by
    have h : (3 : R) * C.r = 0 := by linear_combination e2 + (W.a₁ + C.s) * hs
    exact h3.mul_right_eq_zero.mp h
  have ht : C.t = 0 := by
    have h : (2 : R) * C.t = 0 := by linear_combination e3 - W.a₁ * hr
    exact h2.mul_right_eq_zero.mp h
  obtain ⟨u, r, s, t⟩ := C
  simp only at hu hr hs ht
  subst hu hr hs ht
  exact (WeierstrassCurve.VariableChange.one_def).symm


-- created on 2026-10-05
