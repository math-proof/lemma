import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x y : ℝ}
-- given
  (h₀ : x ∈ Set.Ico a b)
  (h₁ : y ∈ Set.Ico a b) :
-- imply
  Set.Ioc x y ⊆ Set.Ioo a b := by
-- proof
  intro t ht
  obtain ⟨hxt, hty⟩ := ht
  exact ⟨lt_of_le_of_lt h₀.1 hxt, lt_of_le_of_lt hty h₁.2⟩


-- created on 2021-02-27
-- updated on 2023-05-04
