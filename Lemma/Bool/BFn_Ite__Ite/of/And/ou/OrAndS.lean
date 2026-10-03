import sympy.Basic


@[main]
private lemma main
  [Decidable q]
  [Decidable r]
  {a b c : β}
  (R : α → β → Prop)
  (x : α)
-- given
  (h : R x a ∧ q ∨ R x b ∧ ¬q ∧ r ∨ R x c ∧ ¬q ∧ ¬r) :
-- imply
  R x (if q then
    a
  else if r then
    b
  else
    c) := by
-- proof
  grind


-- created on 2026-10-03
