import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
-- given
  (h : 2 ≤ p) :
-- imply
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : LpSpace p d, ‖x.toL2‖ ≤ C * ‖x‖ := by
-- proof
  refine ⟨√d, Real.sqrt_nonneg _, fun x => ?_⟩
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (by omega : 1 ≤ p)⟩
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  calc
    _ ≤ ∑ _i : Fin d, ‖x‖ ^ 2 :=
      sum_le_sum fun i _ => by simpa [toL2] using pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) 2
    _ = _ := by simp


-- created on 2026-09-26