import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.Mul
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ f x) :
-- imply
  deriv (Real.sigmoid ∘ f) x =
    Real.sigmoid (f x) * (1 - Real.sigmoid (f x)) * deriv f x :=
-- proof
  ((Real.hasDerivAt_sigmoid (f x)).comp x h₀.hasDerivAt).deriv


-- created on 2022-01-01
-- updated on 2026-10-17
