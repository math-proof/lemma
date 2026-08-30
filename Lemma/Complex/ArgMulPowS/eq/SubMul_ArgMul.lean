import Lemma.Complex.ArgPow.eq.SubMul_Arg
open Complex


@[main]
private lemma main
  {y z : ℂ}
  {n : ℕ} :
-- imply
  arg (z ^ n * y ^ n) =
    n * arg (z * y) - 2 * π * ⌈n * arg (z * y) / (2 * π) - 1 / 2⌉ := by
-- proof
  rw [← mul_pow]
  exact ArgPow.eq.SubMul_Arg (z * y) n


-- created on 2018-11-06
-- updated on 2026-08-22
