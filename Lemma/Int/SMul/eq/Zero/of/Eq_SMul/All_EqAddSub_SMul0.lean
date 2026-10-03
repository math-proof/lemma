import Mathlib
import sympy.Basic


/--
[AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_sub_mul_add_one_smul_eq_zero_of_comp_self_sub_smul_add_eq_zero_of_apply_eq_smul.lean)
-/
@[main]
private lemma main
  [AddCommGroup V]
  {m : V →+ V}
  {t : ℤ}
  {P : V}
  {c : ℤ}
-- given
  (hm : ∀ T, m (m T) - t • m T + T = 0)
  (hP : m P = c • P) :
-- imply
  (c ^ 2 - t * c + 1) • P = 0 := by
-- proof
  have h := hm P
  rw [hP, map_zsmul, hP, smul_smul] at h
  rw [add_smul, sub_smul, one_smul, mul_comm t c, sq, mul_smul, mul_smul] at *
  simpa [smul_smul, mul_comm] using h


-- created on 2026-10-01
