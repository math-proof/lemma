import sympy.core.power
import Lemma.Algebra.GeSquare_0
import Lemma.Algebra.EqSqrtSquare.of.Ge_0
open Algebra


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : y ≥ 0) :
-- imply
  √(x² * y²) = x * y := by
-- proof
  have := GeSquare_0 (a := x)
  have := Real.sqrt_mul this y²
  rwa [EqSqrtSquare.of.Ge_0 h₀, EqSqrtSquare.of.Ge_0 h₁] at this


-- created on 2025-04-06
