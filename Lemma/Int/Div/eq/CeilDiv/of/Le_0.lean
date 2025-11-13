import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Int.Div.eq.CeilDiv.of.Lt_0
open Nat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d ≤ 0) :
-- imply
  n / d = ⌈n / (d : α)⌉ := by
-- proof
  if h_eq : d = 0 then
    rw [h_eq]
    norm_num
  else
    have := Lt.of.Le.Ne h h_eq
    apply Div.eq.CeilDiv.of.Lt_0 this


-- created on 2025-03-20
-- updated on 2025-03-30
