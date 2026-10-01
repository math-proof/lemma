import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {a b c x : ℝ}
-- given
  (h₀ : c ∈ Set.Ioo a b)
  (h₁ : x ∈ Set.Icc c b) :
-- imply
  c ∈ Set.Ioo a b ∧ x ∈ Set.Icc a b := by
-- proof
  exact ⟨h₀, le_trans h₀.1.le h₁.1, h₁.2⟩


-- created on 2026-09-27
