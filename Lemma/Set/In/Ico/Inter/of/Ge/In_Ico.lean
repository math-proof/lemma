import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c x : ℤ}
-- given
  (h₀ : x ≥ a)
  (h₁ : x ∈ Set.Ico b c) :
-- imply
  x ∈ Set.Ico (max b a) c := by
-- proof
  exact ⟨max_le h₁.1 h₀, h₁.2⟩


-- created on 2023-11-12
