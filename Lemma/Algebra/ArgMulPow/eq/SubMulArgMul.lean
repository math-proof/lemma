import sympy.core.numbers
import Lemma.Algebra.Arg.Pow.eq.Add
open Algebra


@[main]
private lemma main
  {y z : ℂ}
  {n : ℕ}
-- given
  (hn : n > 0) :
-- imply
  arg (z ^ n * y ^ n) =
    n * arg (z * y) - 2 * π * ⌈n * arg (z * y) / (2 * π) - 1 / 2⌉ := by
-- proof
  rw [← mul_pow]
  exact Arg.Pow.eq.Add hn


-- created on 2018-11-06
-- updated on 2026-08-20
