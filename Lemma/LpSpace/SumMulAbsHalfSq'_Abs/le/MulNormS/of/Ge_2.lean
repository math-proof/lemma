import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {x y : LpSpace p d}
-- given
  (h : 2 ≤ p) :
-- imply
  ∑ i, |half_sq' x i| * |y i| ≤ ‖x‖ * ‖y‖ := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpq : ((p : ℝ) / (p - 1)).HolderConjugate p := ((Real.holderConjugate_iff_eq_conjExponent (by linarith)).2 rfl).symm
  have hn : ∀ z : LpSpace p d, (∑ i, |z i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) = ‖z‖ := fun z => by
    rw [PiLp.norm_eq_sum (by simp; linarith) z]
    simp
  have hx : ∀ i, |half_sq' x i| = ‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ ((p : ℝ) - 1) := fun i => by
    simp only [half_sq', PiLp.toLp_apply]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), mul_assoc,
      ← Real.rpow_add_one' (abs_nonneg _) (by linarith)]
    ring_nf
  calc
    _ = ‖x‖ ^ (2 - (p : ℝ)) * ∑ i, |x i| ^ ((p : ℝ) - 1) * |y i| := by
      simp_rw [hx, mul_sum, mul_assoc]
    _ ≤ ‖x‖ ^ (2 - (p : ℝ)) * ((∑ i, |(|x i| ^ ((p : ℝ) - 1))| ^ ((p : ℝ) / (p - 1))) ^ (1 / ((p : ℝ) / (p - 1))) * (∑ i, |(|y i|)| ^ (p : ℝ)) ^ (1 / (p : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.inner_le_Lp_mul_Lq _ _ _ hpq) (by positivity)
    _ = ‖x‖ ^ (2 - (p : ℝ)) * (‖x‖ ^ ((p : ℝ) - 1) * ‖y‖) := by
      have hx' : ∀ i, |(|x i| ^ ((p : ℝ) - 1))| ^ ((p : ℝ) / (p - 1)) = |x i| ^ (p : ℝ) := fun i => by
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        field_simp
      simp_rw [hx', abs_abs, hn y]
      congr 1
      rw [← hn x, ← Real.rpow_mul (sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)]
      congr 1
      field_simp
    _ = _ := by
      rw [← mul_assoc, ← Real.rpow_add' (norm_nonneg x) (by norm_num), show 2 - (p : ℝ) + (p - 1) = 1 by ring, Real.rpow_one]


-- created on 2026-09-26