import Lemma.Real.CosSub.eq.AddMulS
open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : cos x = 0)
  (n : ℕ) :
-- imply
  cos (x - n * π) = 0 := by
-- proof
  rw [CosSub.eq.AddMulS, h, zero_mul, zero_add]
  exact mul_eq_zero.mpr (Or.inr (sin_int_mul_pi n))


-- created on 2018-06-18
