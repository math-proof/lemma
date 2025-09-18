import Lemma.Algebra.Add
open Algebra


@[main, comm]
private lemma main
  [AddSemigroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + (b + c) :=
-- proof
  add_assoc a b c


@[main, comm]
private lemma comm.nat
-- given
  (a b c : ℕ) :
-- imply
  a + b + c = a + (c + b) := by
-- proof
  rw [main]
  rw [Add.comm (a := b)]


@[main, comm]
private lemma Comm
  [AddCommGroup α]
-- given
  (a b c : α) :
-- imply
  a + b + c = a + (c + b) := by
-- proof
  rw [main]
  rw [Add.comm (a := b)]


-- created on 2024-07-01
-- updated on 2025-05-24
