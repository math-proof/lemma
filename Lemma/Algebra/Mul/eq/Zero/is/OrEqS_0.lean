import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [MulZeroClass α] [NoZeroDivisors α]
  {a b : α} :
-- imply
  a * b = 0 ↔ a = 0 ∨ b = 0 :=
-- proof
  mul_eq_zero


-- created on 2024-11-29
