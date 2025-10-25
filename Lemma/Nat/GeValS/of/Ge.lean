import Lemma.Nat.LeValS.of.Le
open Nat


@[main]
private lemma main
  {i j : Fin n}
-- given
  (h : i ≥ j) :
-- imply
  i.val ≥ j.val := 
-- proof
  LeValS.of.Le h


-- created on 2025-06-21
