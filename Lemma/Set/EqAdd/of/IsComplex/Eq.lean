import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x y z : ℂ}
-- given
  (_h₀ : x ∈ (Set.univ : Set ℂ))
  (h₁ : y - x = z) :
-- imply
  y = x + z := by
-- proof
  rw [← h₁]
  ring


-- created on 2026-09-27
