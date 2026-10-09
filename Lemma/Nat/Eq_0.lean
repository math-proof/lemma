import Mathlib
import sympy.Basic

open scoped MatrixGroups
open CongruenceSubgroup

/--
[CuspForm_eq_zero_of_gamma0_one_weight_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CuspForm_eq_zero_of_gamma0_one_weight_two.lean)
-/

private lemma  Gamma0_one_eq_top : Gamma0 1 = ⊤ := by
  ext A
  simp only [Gamma0_mem, Subgroup.mem_top, iff_true]
  exact Subsingleton.elim _ _

private lemma  Gamma0_one_coe_eq_SL : (↑(Gamma0 1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top]
  simp [MonoidHom.range_eq_map]

private lemma  cuspForm_eq_zero_of_eq_SL {Γ : Subgroup (GL (Fin 2) ℝ)} (hΓ : Γ = 𝒮ℒ) {k : ℤ} (hk : k < 12)
    (f : CuspForm Γ k) : f = 0 := by
  subst hΓ
  exact rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve hk) f
@[path]
private lemma main
  {f : CuspForm (CongruenceSubgroup.Gamma0 1) 2} :
-- imply
  f = 0 :=
-- proof
  cuspForm_eq_zero_of_eq_SL Gamma0_one_coe_eq_SL (by norm_num) f


-- created on 2026-10-05
