import Syntax.Logic.Quantifier.Part4
import Initialize.Tactic.Attr.Basic


@[path]
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


-- created on 2018-04-10
-- updated on 2026-10-26
