import Mathlib
import sympy.Basic
import Lemma.ModularCurve.X0
open Polynomial ModularCurve


private lemma  coeff_evalAtJ_neg_natDegree (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d) : (evalAtJ P).coeff (-(d : ℤ)) = (P.coeff d : ℚ) := by
  have hsum : evalAtJ P = ∑ e ∈ Finset.range (d + 1), (P.coeff e : LaurentSeries ℚ) * jq ^ e := by
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hd), map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, map_pow, evalAtJ_X]
    congr 1
    simp [evalAtJ]
  rw [hsum, HahnSeries.coeff_sum]
  rw [Finset.sum_eq_single d]
  · rw [show ((P.coeff d : ℤ) : LaurentSeries ℚ) = HahnSeries.C ((P.coeff d : ℚ)) by rw [← map_intCast (HahnSeries.C (Γ := ℤ) (R := ℚ))],
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeff_jq_pow_self, smul_eq_mul, mul_one]
  ·
    intro e he hed
    rw [Finset.mem_range] at he
    have hlt : e < d := lt_of_le_of_ne (Nat.le_of_lt_succ he) hed
    rw [show ((P.coeff e : ℤ) : LaurentSeries ℚ) = HahnSeries.C ((P.coeff e : ℚ)) by rw [← map_intCast (HahnSeries.C (Γ := ℤ) (R := ℚ))],
      HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, coeff_jq_pow_of_lt (by omega), smul_zero]
  ·
    intro h; exact absurd (Finset.self_mem_range_succ d) h

private lemma  eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero' (P : Polynomial ℤ) (n : ℕ) (hP : P.natDegree ≤ n) (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) : P = 0 := by
  by_contra hne
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hne
  have := coeff_evalAtJ_neg_natDegree P P.natDegree le_rfl
  rw [h _ (by omega) (by omega)] at this
  exact hlc (by exact_mod_cast this.symm)
/--
[ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero.lean)
-/
@[path]
private lemma main
  {P : Polynomial ℤ}
  {n : ℕ}
-- given
  (hP : P.natDegree ≤ n)
  (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) :
-- imply
  P = 0 :=
-- proof
  eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero' P n hP h


-- created on 2026-10-23
