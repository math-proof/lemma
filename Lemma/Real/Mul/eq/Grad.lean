import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Real.Mul.eq.Grad |
| comm | Real.Grad.eq.Mul |
-/
@[path, comm]
private lemma main
  {f : ℝ → ℝ}
  {x y : ℝ} :
-- imply
  deriv f x * y = deriv (fun x' => f x' * y) x :=
-- proof
  (deriv_mul_const_field y).symm


-- created on 2026-10-01
