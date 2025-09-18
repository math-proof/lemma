import Lemma.Algebra.Mul
open Algebra


@[main, comm]
private lemma main
  [DivInvMonoid α]
  (a b c : α) :
-- imply
  a * b / c = a * (b / c) :=
-- proof
  mul_div_assoc a b c


@[main, comm]
private lemma Comm
  [Semifield α]
  (a b c : α) :
-- imply
  b * a / c = a * (b / c) := by
-- proof
  rw [← main]
  rw [Mul.comm]

-- created on 2024-07-01
