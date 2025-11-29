import Lemma.Nat.Mul
open Nat


@[main, comm]
private lemma main
  [Semigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (b * c) :=
-- proof
  mul_assoc a b c


@[main, comm]
private lemma Comm
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = a * (c * b) := by
-- proof
  rw [main]
  rw [Mul.comm (a := b)]


-- created on 2024-07-01
-- updated on 2025-11-29
