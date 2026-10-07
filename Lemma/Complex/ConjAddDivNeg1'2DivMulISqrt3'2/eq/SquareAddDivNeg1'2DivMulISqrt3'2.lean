import sympy.functions.elementary.complexes
import sympy.Basic
import Lemma.Complex.SquareSqrt3.eq.Three
open Complex


@[main]
private lemma main :
-- imply
  ~(-1 / 2 + Complex.I * √3 / 2 : ℂ) = (-1 / 2 + Complex.I * √3 / 2) ^ 2 := by
-- proof
  have e : ~(-1 / 2 + Complex.I * √3 / 2 : ℂ) = -1 / 2 - Complex.I * √3 / 2 := by
    simp only [Complex.conj, map_add, map_div₀, map_neg, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  rw [e]
  linear_combination (-(Complex.I ^ 2) / 4) * SquareSqrt3.eq.Three + (-3 / 4 : ℂ) * Complex.I_sq


-- created on 2026-10-07
