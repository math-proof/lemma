import Mathlib.Data.Complex.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
  {e : ℝ}
-- given
  (h₀ : x = e) :
-- imply
  x ∈ Set.range ((↑) : ℝ → ℂ) :=
-- proof
  ⟨e, h₀.symm⟩


-- created on 2020-05-03
