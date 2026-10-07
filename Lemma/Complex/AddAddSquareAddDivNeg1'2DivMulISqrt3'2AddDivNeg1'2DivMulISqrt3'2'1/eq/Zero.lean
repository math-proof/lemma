import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.SquareSqrt3.eq.Three
open Complex


@[main]
private lemma main :
-- imply
  (-1 / 2 + Complex.I * √3 / 2 : ℂ) ^ 2 + (-1 / 2 + Complex.I * √3 / 2) + 1 = 0 := by
-- proof
  linear_combination (Complex.I ^ 2 / 4) * SquareSqrt3.eq.Three + (3 / 4 : ℂ) * Complex.I_sq


-- created on 2026-10-07
