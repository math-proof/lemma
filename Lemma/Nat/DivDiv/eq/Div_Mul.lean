import sympy.Basic


@[main, comm]
private lemma main
-- given
  (a b c : ℕ) :
-- imply
  a / b / c = a / (b * c) :=
-- proof
  Nat.div_div_eq_div_mul a b c


-- created on 2025-10-08
