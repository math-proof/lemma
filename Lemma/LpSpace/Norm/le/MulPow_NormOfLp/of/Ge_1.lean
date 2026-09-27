import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {x : LpSpace p d}
-- given
  (h : 1 ≤ p) :
-- imply
  ‖x‖ ≤ (d : ℝ) ^ (1 / (p : ℝ)) * ‖WithLp.ofLp x‖ := by
-- proof
  have hp : (0 : ℝ) < p := by exact_mod_cast h
  rw [PiLp.norm_eq_sum (by simpa using hp) x]
  simp only [ENNReal.toReal_natCast]
  calc
    _ ≤ (∑ _i : Fin d, ‖WithLp.ofLp x‖ ^ (p : ℝ)) ^ (1 / (p : ℝ)) :=
      Real.rpow_le_rpow (sum_nonneg fun i _ => by positivity)
        (sum_le_sum fun i _ => Real.rpow_le_rpow (norm_nonneg _) (norm_le_pi_norm _ i) hp.le) (by positivity)
    _ = _ := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp.ne', Real.rpow_one]


-- created on 2026-09-26