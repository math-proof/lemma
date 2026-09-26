import sympy.vector.lp_space
import sympy.Basic
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {z v : LpSpace p d}
-- given
  (h : 2 < p) :
-- imply
  ∑ i, p * (p - 1) * |z i| ^ (p - 2) * v i ^ 2 ≤ p * (p - 1) * ‖z‖ ^ (p - 2) * ‖v‖ ^ 2 := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  have hp : (2 : ℝ) < p := by exact_mod_cast h
  have hp2' : (p : ℝ) - 2 ≠ 0 := by linarith
  have hp2 : ((p - 2 : ℕ) : ℝ) = p - 2 := by push_cast [Nat.cast_sub h.le]; ring
  have hpq : ((p : ℝ) / (p - 2)).HolderConjugate ((p : ℝ) / 2) :=
    ⟨by field_simp; ring, by apply div_pos <;> linarith, by positivity⟩
  have hn : ∀ w : LpSpace p d, (∑ i, |w i| ^ (p : ℝ)) ^ (1 / (p : ℝ)) = ‖w‖ := fun w => by
    rw [PiLp.norm_eq_sum (by simp; linarith) w]
    simp
  simp_rw [mul_assoc (↑p * (↑p - 1) : ℝ)]
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by nlinarith)
  calc
    _ ≤ (∑ i, |(|z i| ^ (p - 2))| ^ ((p : ℝ) / (p - 2))) ^ (1 / ((p : ℝ) / (p - 2))) * (∑ i, |v i ^ 2| ^ ((p : ℝ) / 2)) ^ (1 / ((p : ℝ) / 2)) :=
      Real.inner_le_Lp_mul_Lq _ _ _ hpq
    _ = _ := by
      have hz : ∀ i, |(|z i| ^ (p - 2))| ^ ((p : ℝ) / (p - 2)) = |z i| ^ (p : ℝ) := fun i => by
        rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _), ← Real.rpow_natCast, hp2, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        field_simp
      have hv : ∀ i, |v i ^ 2| ^ ((p : ℝ) / 2) = |v i| ^ (p : ℝ) := fun i => by
        rw [abs_pow, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
        congr 1
        push_cast
        field_simp
      simp_rw [hz, hv]
      rw [← hn z, ← hn v, ← Real.rpow_natCast _ (p - 2), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (sum_nonneg fun i _ => by positivity), ← Real.rpow_mul (sum_nonneg fun i _ => by positivity), hp2]
      congr 2 <;> push_cast <;> field_simp


-- created on 2026-09-26