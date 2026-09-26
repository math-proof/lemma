import Mathlib.Data.Complex.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
  {e : ℝ}
-- given
  (h₀ : x = e) :
-- imply
  x ∈ Set.range ((↑) : ℝ → ℂ) :=
-- proof
  ⟨e, h₀.symm⟩


-- created on 2026-09-26
