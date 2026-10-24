import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x < b) :
-- imply
  x ∈ Set.Ico a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2021-05-24
-- updated on 2026-10-17
