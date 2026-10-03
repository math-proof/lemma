import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {α : Type*}
  {g f h : α} :
-- imply
  (if p then g else if ¬p ∧ ¬q then f else h) = (if p then g else if ¬q then f else h) := by
-- proof
  split_ifs <;> tauto


-- created on 2026-10-03
