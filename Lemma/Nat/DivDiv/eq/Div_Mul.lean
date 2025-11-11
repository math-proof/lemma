import Lemma.Nat.Mul
open Nat


@[main, comm]
private lemma main
-- given
  (a b c : ℕ) :
-- imply
  a / b / c = a / (b * c) :=
-- proof
  Nat.div_div_eq_div_mul a b c


@[main, comm]
private lemma comm'
-- given
  (a b c : ℕ) :
-- imply
  a / b / c = a / (c * b) := by
-- proof
  rw [main]
  rw [Mul.comm]


-- created on 2025-10-08
-- updated on 2025-10-24
