import Macro.Logic.Quantifier.Part4
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p q f : α → Prop}
-- given
  (h : (∃ x | p x, f x) ∨ ∃ x | q x, f x) :
-- imply
  ∃ x | p x ∨ q x, f x := by
-- proof
  aesop


-- created on 2023-10-22
-- updated on 2026-10-26
