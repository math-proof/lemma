import Lemma.List.LengthCons.eq.AddLength_1
import Lemma.Nat.Add
open List Nat


@[main]
private lemma main
-- given
  (a : α)
  (l : List α) :
-- imply
  (a :: l).length = 1 + l.length := by
-- proof
  have := LengthCons.eq.AddLength_1 a l
  rwa [Add.comm] at this


-- created on 2025-05-08
-- updated on 2026-07-11
