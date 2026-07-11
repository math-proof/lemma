import sympy.Basic
open Nat


@[main]
private lemma main
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).length = l.length + 1 :=
-- proof
  List.length_cons


-- created on 2026-07-11
