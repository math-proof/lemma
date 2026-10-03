import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
  {α : Type*}
  {x y z : α}
-- given
  (h : (if p then x else y) = z)
  (e : p ↔ q) :
-- imply
  (if q then x else y) = z := by
-- proof
  grind


-- created on 2026-10-03
