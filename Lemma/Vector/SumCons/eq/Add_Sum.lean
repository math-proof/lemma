import Def.Data.Vector.Basic
import Instance.Data.Vector.Vector
import Lemma.List.SumCons.eq.Add_Sum
open List


@[path]
private lemma main
  [Add α] [Zero α]
-- given
  (a : α)
  (l : List.Vector α n) :
-- imply
  (a ::ᵥ l).sum = a + l.sum :=
-- proof
  SumCons.eq.Add_Sum


-- created on 2025-10-03
-- updated on 2026-11-20
