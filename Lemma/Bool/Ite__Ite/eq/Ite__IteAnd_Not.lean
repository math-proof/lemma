import sympy.Basic


@[main, comm]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (a b c : α) :
-- imply
  (if p then
    a
  else if q then
    b
  else
    c) = if p then
    a
  else if q ∧ ¬p then
    b
  else
    c := by
-- proof
  grind


-- created on 2018-01-30
-- updated on 2026-08-06
