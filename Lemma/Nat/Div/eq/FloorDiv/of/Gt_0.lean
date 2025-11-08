import Lemma.Nat.OfNat.eq.Cast
import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
open Int Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℕ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : α)⌋ := by
-- proof
  simp [Div.eq.FloorDiv.of.Gt_0 (α := α) (by simpa) (d := d)]


-- created on 2025-03-17
-- updated on 2025-10-08
