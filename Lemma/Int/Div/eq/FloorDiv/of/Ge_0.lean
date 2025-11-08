import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
import Lemma.Nat.Gt.is.Ge.Ne
open Int Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d ≥ 0) :
-- imply
  n / d = ⌊n / (d : α)⌋ := by
-- proof
  if h_d : d = 0 then
    rw [h_d]
    norm_num
  else
    apply Div.eq.FloorDiv.of.Gt_0
    apply Gt.of.Ge.Ne h h_d


-- created on 2025-03-20
-- updated on 2025-03-30
