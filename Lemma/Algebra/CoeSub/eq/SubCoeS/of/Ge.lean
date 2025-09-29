import sympy.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne α]
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  ((a - b : ℕ) : α) = a - b :=
-- proof
  Nat.cast_sub h


-- created on 2025-03-28
