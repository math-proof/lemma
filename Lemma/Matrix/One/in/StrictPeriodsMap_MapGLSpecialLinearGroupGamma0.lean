import Mathlib
import sympy.Basic

open scoped MatrixGroups

/--
[CongruenceSubgroup_one_mem_strictPeriods_Gamma0](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CongruenceSubgroup_one_mem_strictPeriods_Gamma0.lean)
-/
@[path]
private lemma main
  {N : ℕ} :
-- imply
  (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
-- proof
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]
  have h := Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT
  rw [h]
  exact AddSubgroup.mem_zmultiples (1 : ℝ)


-- created on 2026-10-05
