import sympy.Basic
import sympy.integrals.integrals
open MeasureTheory


@[main, comm]
private lemma main
  {h : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x : ℝ, h * f x = h * ∫ x : ℝ, f x :=
-- proof
  integral_const_mul h f


-- created on 2026-09-26
