import sympy.core.numbers
import Lemma.Algebra.Arg.eq.Add.of.Ne_0.Ne_0
open Algebra


@[main]
private lemma main
  {x y : ℂ} :
-- imply
  arg (x * y) =
    if x = 0 ∨ y = 0 then
      0
    else
      arg x + arg y - 2 * π * ⌈(arg x + arg y) / (2 * π) - 1 / 2⌉ := by
-- proof
  split_ifs with h
  ·
    rcases h with hx | hy
    ·
      rw [hx, zero_mul, Complex.arg_zero]
    ·
      rw [hy, mul_zero, Complex.arg_zero]
  ·
    push Not at h
    exact Arg.eq.Add.of.Ne_0.Ne_0 h.1 h.2


-- created on 2018-10-26
-- updated on 2026-08-20
