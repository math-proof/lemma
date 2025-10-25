import Lemma.Nat.LtValS.of.Lt
open Nat


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i > j) :
-- imply
  i.val > j.val :=
-- proof
  LtValS.of.Lt h


-- created on 2025-06-21
