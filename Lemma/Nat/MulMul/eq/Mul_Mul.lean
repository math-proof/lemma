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
  grind


@[main, comm]
private lemma swap
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = b * (a * c) := by
-- proof
  grind


@[main, comm]
private lemma rotate
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = b * (c * a) := by
-- proof
  grind


@[main, comm]
private lemma permute
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = c * (a * b) := by
-- proof
  grind


@[main, comm]
private lemma reverse
  [CommSemigroup α]
  {a b : α} :
-- imply
  a * b * c = c * (b * a) := by
-- proof
  grind


-- created on 2024-07-01
-- updated on 2026-08-02
