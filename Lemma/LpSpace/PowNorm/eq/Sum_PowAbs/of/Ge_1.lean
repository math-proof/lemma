import sympy.vector.lp_space
import sympy.Basic
open Finset


@[main]
private lemma main
  {p d : ℕ}
  {x : LpSpace p d}
-- given
  (h : 1 ≤ p) :
-- imply
  ‖x‖ ^ p = ∑ i, |x i| ^ p := by
-- proof
  have hp : (0 : ℝ) < p := by exact_mod_cast h
  rw [PiLp.norm_eq_sum (by simpa using hp) x]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (sum_nonneg fun i _ => by positivity), one_div,
    inv_mul_cancel₀ hp.ne', Real.rpow_one]


-- created on 2026-09-26