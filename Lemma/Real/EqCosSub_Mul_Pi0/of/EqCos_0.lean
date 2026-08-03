import Lemma.Real.CosSub.eq.AddCosCos_SinSin
open Real


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : Real.cos x = 0)
  (n : ℕ) :
-- imply
  Real.cos (x - n * Real.pi) = 0 := by
-- proof
  rw [CosSub.eq.AddCosCos_SinSin, h, zero_mul, zero_add]
  exact mul_eq_zero.mpr (Or.inr (sin_int_mul_pi n))


-- created on 2018-06-18
