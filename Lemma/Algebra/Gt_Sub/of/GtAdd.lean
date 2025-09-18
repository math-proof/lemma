import Lemma.Algebra.LtSub.of.Lt_Add
open Algebra


@[main]
private lemma left
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b > c) :
-- imply
  b > c - a :=
-- proof
  LtSub.of.Lt_Add.left h


@[main]
private lemma main
  [OrderedAddCommGroup α]
  {a b c : α}
-- given
  (h : a + b > c) :
-- imply
  a > c - b :=
-- proof
  LtSub.of.Lt_Add h


-- created on 2024-11-26
