import Syntax.Logic.Quantifier.Part4
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : α → Prop}
  {q : β → Prop}
  {r : α → Prop}
  {s : β → Prop}
-- given
  (h₀ : ∃ x | r x, p x)
  (h₁ : ∃ y | s y, q y) :
-- imply
  ∃ x | r x, ∃ y | s y, p x ∧ q y := by
-- proof
  obtain ⟨x, hr, hp⟩ := h₀
  obtain ⟨y, hs, hq⟩ := h₁
  exact ⟨x, hr, y, hs, hp, hq⟩


-- created on 2019-02-08
-- updated on 2026-10-26
