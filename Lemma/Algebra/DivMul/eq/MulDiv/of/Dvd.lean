import sympy.Basic


@[main, comm]
private lemma main
  {a b : ℕ}
-- given
  (h : b ∣ a)
  (c : ℕ):
-- imply
  a * c / b = a / b * c :=
-- proof
  Nat.mul_div_right_comm h c


-- created on 2025-07-05
