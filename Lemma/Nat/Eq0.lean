import Mathlib
import sympy.Basic
open scoped MatrixGroups CongruenceSubgroup


private lemma Gamma0_one_eq_top :
  (CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private lemma coe_Gamma0_one_eq_SL :
  ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  rw [Gamma0_one_eq_top]
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range]

private lemma cuspForm_eq_zero_of_subgroup_eq {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℝ)}
  (h : Γ₂ = Γ₁) {k : ℤ} (H : ∀ g : CuspForm Γ₂ k, g = 0) (f : CuspForm Γ₁ k) :
  f = 0 := by
  subst h; exact H f
/--
[ModularForm_S2_Gamma0_one_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_S2_Gamma0_one_eq_zero.lean)
-/
@[path]
private lemma main
  {f : CuspForm (CongruenceSubgroup.Gamma0 1) 2} :
-- imply
  f = 0 :=
-- proof
  cuspForm_eq_zero_of_subgroup_eq coe_Gamma0_one_eq_SL.symm
    (fun g => rank_zero_iff_forall_zero.mp
      (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) g) f


-- created on 2026-10-23
