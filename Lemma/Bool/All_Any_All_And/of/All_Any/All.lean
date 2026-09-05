import sympy.Basic


@[main]
private lemma main
  {p q : α → ι → Prop}
-- given
  (h₀ : ∀ x : α, ∀ i : ι, p x i)
  (h₁ : ∀ x : α, ∃ j : ι, q x j) :
-- imply
  ∀ x : α, ∃ j, ∀ i : ι, p x i ∧ q x j := by
-- proof
  intro x
  obtain ⟨j, hq⟩ := h₁ x
  use j
  grind


-- created on 2018-12-03
