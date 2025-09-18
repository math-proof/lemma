import Lemma.Basic


@[main, comm]
private lemma main
  [DivisionCommMonoid α]
  (a b c : α) :
-- imply
  a / b / c = a / (b * c)  := by
-- proof
  rw [div_mul_eq_div_div]


@[main, comm]
private lemma nat
  (a b c : ℕ) :
-- imply
  a / b / c = a / (b * c)  :=
-- proof
  Nat.div_div_eq_div_mul a b c

-- created on 2024-07-01
