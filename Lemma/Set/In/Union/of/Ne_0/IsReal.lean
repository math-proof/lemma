import sympy.functions.elementary.complexes
import sympy.Basic


@[main]
private lemma main
  {x : ℂ}
-- given
  (h₀ : x ≠ 0)
  (h₁ : x ∈ Set.range Complex.ofReal) :
-- imply
  x ∈ Set.range Complex.ofReal \ {0} := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2023-05-02
