import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
  [Mul α][One α]
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).prod = a * l.prod :=
-- proof
  List.prod_cons


-- created on 2025-06-14
