import Lemma.Nat.Mod.eq.Sub_Mul_Div
import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
open Int Nat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  n % d = n - d * ⌊n / (d : α)⌋ := by
-- proof
  rw [← Div.eq.FloorDiv.of.Gt_0 h]
  apply Mod.eq.Sub_Mul_Div


-- created on 2018-02-25
