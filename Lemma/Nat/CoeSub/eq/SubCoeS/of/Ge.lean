import sympy.Basic


@[main, comm]
private lemma main
  [AddGroupWithOne Z]
  {a b : ℕ}
-- given
  (h : a ≥ b) :
-- imply
  ((a - b : ℕ) : Z) = a - b :=
-- proof
  Nat.cast_sub h


-- created on 2025-03-28
