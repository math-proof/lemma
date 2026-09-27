import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
open Finset LpSpace


@[main]
private lemma main
  {p d : ℕ}
  {x : LpSpace p d}
-- given
  (h : 1 ≤ p) :
-- imply
  inner ℝ (half_sq' x).toL2 x.toL2 = ‖x‖ ^ 2 := by
-- proof
  have : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast h⟩
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast h
  have key : ∀ i, x i * (‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ ((p : ℝ) - 2) * x i) = ‖x‖ ^ (2 - (p : ℝ)) * |x i| ^ p := fun i => by
    rw [mul_comm, mul_assoc, mul_assoc, ← pow_two, ← sq_abs, ← Real.rpow_natCast |x i| 2,
      ← Real.rpow_add' (abs_nonneg _) (by push_cast; linarith), ← Real.rpow_natCast]
    push_cast
    ring_nf
  simp only [toL2, half_sq', PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
  simp_rw [key]
  rw [← mul_sum, ← PowNorm.eq.Sum_PowAbs.of.Ge_1 h, ← Real.rpow_natCast ‖x‖ p,
    ← Real.rpow_add' (norm_nonneg x) (by norm_num), sub_add_cancel, Real.rpow_two]


-- created on 2026-09-26