import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p q : α → ι → Prop}
  {r : α → Prop}
  {s : ι → Prop}
-- given
  (h₀ : ∀ y | s y, ∀ x | r x, q x y)
  (h₁ : ∀ y | s y, ∃ x | r x, p x y) :
-- imply
  ∀ y | s y, ∃ x | r x, q x y ∧ p x y := by
-- proof
  intro y hy
  obtain ⟨x, hr, hp⟩ := h₁ y hy
  exact ⟨x, hr, h₀ y hy x hr, hp⟩


-- created on 2019-03-13
-- updated on 2026-09-09
