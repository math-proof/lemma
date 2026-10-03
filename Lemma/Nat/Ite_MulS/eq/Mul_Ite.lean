import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {α : Type*} [Mul α]
  {r g f h : α} :
-- imply
  (if p then r * g else if q then r * f else r * h) = r * (if p then g else if q then f else h) := by
-- proof
  split_ifs <;> rfl


-- created on 2026-10-03
