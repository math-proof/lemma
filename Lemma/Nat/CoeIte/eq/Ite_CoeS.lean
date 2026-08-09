import sympy.Basic


@[main]
private lemma main
  [Decidable p]
  [NatCast α]
  (a b : ℕ) :
-- imply
  ((if p then
    a
  else
    b) : ℕ) = if p then
    (a : α)
  else
    (b : α) := by
-- proof
  grind


-- created on 2026-08-08
