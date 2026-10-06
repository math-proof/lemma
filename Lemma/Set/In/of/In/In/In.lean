import sympy.Basic


@[main]
private lemma main
  {a b c d x y z : ℝ}
-- given
  (h₀ : x ∈ Set.Ioc a b)
  (h₁ : y ∈ Set.Ico c d)
  (h₂ : z ∈ Set.Ioc x y) :
-- imply
  z ∈ Set.Ioo a d := by
-- proof
  obtain ⟨hx₀, _⟩ := h₀
  obtain ⟨_, hy₁⟩ := h₁
  obtain ⟨hz₀, hz₁⟩ := h₂
  exact ⟨lt_trans hx₀ hz₀, lt_of_le_of_lt hz₁ hy₁⟩


-- created on 2021-02-24
