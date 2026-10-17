import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : x ≤ a)
  (h₁ : b ≤ x) :
-- imply
  x ∈ Set.Icc b a :=
-- proof
  ⟨h₁, h₀⟩


-- created on 2026-10-11
-- updated on 2026-10-17
