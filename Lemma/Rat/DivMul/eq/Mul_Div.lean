import Lemma.Nat.Mul
open Nat


@[main, comm]
private lemma main
  [DivInvMonoid α]
-- given
  (a b c : α) :
-- imply
  a * b / c = a * (b / c) :=
-- proof
  mul_div_assoc a b c


@[main, comm]
private lemma comm'
  [Semifield α]
-- given
  (a b c : α) :
-- imply
  b * a / c = a * (b / c) := by
-- proof
  rw [← main]
  rw [Mul.comm]

-- created on 2024-07-01
