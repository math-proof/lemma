import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {e a b c : ℝ}
-- given
  (h : e ∈ Set.Icc a b)
  (_hc : c ∈ Set.Icc a b) :
-- imply
  e ∈ Set.Ico a c ∨ e ∈ Set.Icc c b := by
-- proof
  obtain ⟨h₁, h₂⟩ := h
  if hce : e < c then
    exact Or.inl ⟨h₁, hce⟩
  else
    exact Or.inr ⟨not_lt.mp hce, h₂⟩


-- created on 2023-04-18
