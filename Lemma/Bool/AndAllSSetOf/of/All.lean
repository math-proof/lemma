import sympy.concrete.quantifier
import sympy.Basic


@[main]
private lemma main
  {p : α → Prop}
-- given
  (h : ∀ e, p e)
  (q : α → Prop):
-- imply
  (∀ e | q e, p e) ∧ ∀ e | ¬q e, p e := by
-- proof
  constructor <;>
  ·
    intro e h_q
    exact h e


-- created on 2025-04-28
-- updated on 2025-04-29
