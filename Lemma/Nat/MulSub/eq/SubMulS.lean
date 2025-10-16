import sympy.Basic


@[main, comm]
private lemma main
-- given
  (x a b : ℕ) :
-- imply
  (a - b) * x = a * x - b * x :=
-- proof
  Nat.sub_mul a b x


-- created on 2025-10-16
