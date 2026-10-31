import Mathlib.Analysis.Real.Sqrt
import Initialize.Tactic.Attr.Basic
open Real


@[path]
private lemma main
  {n : ℕ}
-- given
  (hn : 0 < n)
  (s : ℝ) :
-- imply
  (n : ℝ).sqrt⁻¹ * s = (n : ℝ).sqrt * (s / n) := by
-- proof
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsqrt : 0 < (n : ℝ).sqrt := sqrt_pos.mpr hnpos
  rw [inv_mul_eq_iff_eq_mul₀ hsqrt.ne']
  rw [← mul_assoc, ← pow_two, sq_sqrt hnpos.le, mul_div_cancel₀ _ hnpos.ne']


-- created on 2026-10-31
