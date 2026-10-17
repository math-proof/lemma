import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : b ≥ x) :
-- imply
  x ∈ Set.Ioc a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2026-10-11
-- updated on 2026-10-17
