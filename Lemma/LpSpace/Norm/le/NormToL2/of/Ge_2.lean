import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {x : LpSpace p d}
-- given
  (h : 2 ≤ p) :
-- imply
  ‖x‖ ≤ ‖x.toL2‖ := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  have hs : ∀ i, |x i| ≤ ‖x.toL2‖ := fun i => by
    simpa [toL2] using PiLp.norm_apply_le (p := 2) (β := fun _ : Fin d => ℝ) x.toL2 i
  refine (pow_le_pow_iff_left₀ (norm_nonneg x) (norm_nonneg x.toL2) (by omega : p ≠ 0)).1 ?_
  rw [PowNorm.eq.Sum_PowAbs.of.Ge_1 (by omega)]
  calc
    _ = ∑ i, |x i| ^ (p - 2) * |x i| ^ 2 := by
      refine sum_congr rfl fun i _ => ?_
      rw [← pow_add, Nat.sub_add_cancel h]
    _ ≤ ∑ i, ‖x.toL2‖ ^ (p - 2) * |x i| ^ 2 :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hs i) _) (sq_nonneg _)
    _ = ‖x.toL2‖ ^ (p - 2) * ‖x.toL2‖ ^ 2 := by
      rw [← mul_sum, EuclideanSpace.norm_sq_eq]
      simp [toL2]
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel h]


-- created on 2026-09-26