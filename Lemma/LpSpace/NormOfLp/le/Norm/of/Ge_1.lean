import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {x : LpSpace p d}
-- given
  (h : 1 ≤ p) :
-- imply
  ‖WithLp.ofLp x‖ ≤ ‖x‖ := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast h⟩
  exact pi_norm_le_iff_of_nonneg (norm_nonneg _) |>.2 fun i => PiLp.norm_apply_le x i


-- created on 2026-09-26