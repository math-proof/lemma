import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ioo a b)
  (h₁ : y ∈ Set.Ioo a b) :
-- imply
  Set.Ico x y ⊆ Set.Ioo a b := by
-- proof
  intro t ht
  obtain ⟨hxt, hty⟩ := ht
  exact ⟨lt_of_lt_of_le h₀.1 hxt, lt_trans hty h₁.2⟩


-- created on 2020-11-23
