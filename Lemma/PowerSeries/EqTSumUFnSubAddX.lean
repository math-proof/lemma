import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[PowerSeries_taylorShift_X_sub_C](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_taylorShift_X_sub_C.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  (w a : L) :
  -- imply
  (PowerSeries.mk fun n => tsum fun k : ℕ =>
    PowerSeries.coeff (n + k) (PowerSeries.X - PowerSeries.C w) * ((n + k).choose n : L) * a ^ k) =
    PowerSeries.C (a - w) + PowerSeries.X := by
  -- proof
  ext n
  rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C, PowerSeries.coeff_X]
  induction n with
  | zero =>
    have hvanish : ∀ k ∉ ({0, 1} : Finset ℕ), PowerSeries.coeff (0 + k) (PowerSeries.X - PowerSeries.C w) * ((0 + k).choose 0 : L) * a ^ k = 0 := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      have h2 : 2 ≤ 0 + k := by
        omega
      simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    rw [tsum_eq_sum hvanish]
    rw [Finset.sum_pair (by norm_num)]
    simp [PowerSeries.coeff_X]
    ring
  | succ n =>
    induction n with
    | zero =>
      have hvanish : ∀ k, k ≠ 0 → PowerSeries.coeff (1 + k) (PowerSeries.X - PowerSeries.C w) * ((1 + k).choose 1 : L) * a ^ k = 0 := by
        intro k hk
        simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp
      rw [tsum_eq_single 0 hvanish]
      simp [PowerSeries.coeff_X]
    | succ n =>
      have hzero : (fun k : ℕ => PowerSeries.coeff (n + 1 + 1 + k) (PowerSeries.X - PowerSeries.C w) *
          ((n + 1 + 1 + k).choose (n + 1 + 1) : L) * a ^ k) = fun _ => 0 := by
        funext k
        simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        simp
      rw [hzero, tsum_zero, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]


-- created on 2026-10-20
