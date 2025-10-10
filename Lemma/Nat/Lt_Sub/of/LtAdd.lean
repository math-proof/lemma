import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  a < c - b :=
-- proof
  Nat.lt_sub_of_add_lt h


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  b < c - a := by
-- proof
  rw [Add.comm] at h
  apply main h


-- created on 2025-10-10
