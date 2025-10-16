import Lemma.Nat.LeSub.is.Le_Add
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a + b ≥ c) :
-- imply
  a ≥ c - b :=
-- proof
  LeSub.of.Le_Add h


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h : a + b ≥ c) :
-- imply
  b ≥ c - a :=
-- proof
  LeSub.of.Le_Add.left h


-- created on 2025-10-16
