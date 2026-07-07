import Lemma.Nat.Add
open Nat


@[main, comm]
private lemma main
  [SubNegMonoid α]
-- given
  (a b c : α) :
-- imply
  a + b - c = a + (b - c) :=
-- proof
  add_sub_assoc a b c


@[main, comm]
private lemma Comm
  [AddCommGroup α]
-- given
  (a b c : α) :
-- imply
  a + b - c = b + (a - c) := by
-- proof
  rw [Add.comm]
  rw [main]


-- created on 2024-07-01
-- updated on 2026-07-07
