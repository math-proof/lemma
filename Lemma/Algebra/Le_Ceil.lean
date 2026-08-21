import Lemma.Nat.Le.of.Ge
import Lemma.Rat.GeCeil
open Nat Rat


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  x ≤ ⌈x⌉ := by
-- proof
  apply Le.of.Ge
  apply GeCeil


-- created on 2018-10-28
-- updated on 2026-08-20
