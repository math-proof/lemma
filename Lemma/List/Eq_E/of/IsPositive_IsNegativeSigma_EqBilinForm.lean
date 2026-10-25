import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.GeometricRepresentation.Part4
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.Roots
open CoxeterGroup


/--
[isPositive_sigma_isNegative_eq_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/SignChangeExchangeFinal.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {t : B}
  {v : B → ℝ}
-- given
  (hpos : IsPositive v)
  (hneg_sigma : IsNegative (sigma M t v))
  (hform : bilinForm M v v = 1) :
-- imply
  v = e t := by
-- proof
  have hvu : ∀ u, u ≠ t → v u = 0 := by
    intro u hu
    have h1 := hpos u
    have h2 := hneg_sigma u
    simp only [sigma] at h2
    have he : e t u = 0 := by simp [e, hu]
    rw [he, mul_zero, sub_zero] at h2
    linarith
  have hv_eq : v = v t • e t := by
    ext u
    if hu : u = t then
      subst hu
      simp [e, Pi.smul_apply]
    else
      rw [hvu u hu]
      simp [e, hu, Pi.smul_apply]
  rw [hv_eq, bilinForm_smul_left, bilinForm_smul_right, bilinForm_e_e, formVal_diag] at hform
  have hvt_pos := hpos t
  have hvt_eq : v t = 1 := by
    nlinarith [mul_self_nonneg (v t)]
  rw [hv_eq, hvt_eq, one_smul]


-- created on 2026-10-24
