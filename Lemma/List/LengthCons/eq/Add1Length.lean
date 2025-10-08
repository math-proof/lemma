import Lemma.Nat.Add
open Nat


@[main]
private lemma main
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).length = 1 + l.length := by
-- proof
  have := List.length_cons (a := a) (as := l)
  rwa [Add.comm] at this


-- created on 2025-05-08
