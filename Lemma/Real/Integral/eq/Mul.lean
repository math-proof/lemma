import sympy.Basic
import sympy.integrals.integrals
open MeasureTheory


@[path, comm]
private lemma main
  {h : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x : ℝ, h * f x = h * ∫ x : ℝ, f x :=
-- proof
  integral_const_mul h f


-- created on 2023-03-27
