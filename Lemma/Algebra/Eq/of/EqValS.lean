import stdlib.List.Vector
import Lemma.Logic.EqUFnS.of.Eq
open Logic


@[main]
private lemma fin
  {a b : Fin n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b :=
-- proof
  Fin.eq_of_val_eq h


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : a.val = b.val) :
-- imply
  a = b :=
-- proof
  List.Vector.eq a b h


-- created on 2024-07-01
-- updated on 2025-05-11
