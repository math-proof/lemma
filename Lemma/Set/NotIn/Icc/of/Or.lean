import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {e a b : ℝ}
-- given
  (h₀ : e < a ∨ e ≥ b) :
-- imply
  e ∉ Set.Ico a b := by
-- proof
  intro h₁
  obtain hlt | hge := h₀
  · linarith [h₁.1]
  · linarith [h₁.2]


-- created on 2021-06-12
-- updated on 2026-10-26
