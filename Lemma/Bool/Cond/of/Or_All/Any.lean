import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p r : α → Prop}
  {q : Prop}
-- given
  (h₀ : ∃ x | r x, p x)
  (h₁ : q ∨ ∀ x | r x, ¬p x) :
-- imply
  q := by
-- proof
  obtain ⟨x, hr, hp⟩ := h₀
  exact h₁.resolve_right (fun h => h x hr hp)


-- created on 2019-02-21
-- updated on 2026-09-09
