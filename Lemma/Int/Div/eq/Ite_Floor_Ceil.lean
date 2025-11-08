import Lemma.Int.Div.eq.CeilDiv.of.Lt_0
import Lemma.Int.Div.eq.FloorDiv.of.Ge_0
open Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ} :
-- imply
  n / d =
    if d < 0 then
      ⌈n / (d : α)⌉
    else
      ⌊n / (d : α)⌋ := by
-- proof
  split_ifs with h
  ·
    apply Div.eq.CeilDiv.of.Lt_0 (n := n) h
  ·
    simp at h
    apply Div.eq.FloorDiv.of.Ge_0
    simpa


-- created on 2025-03-16
-- updated on 2025-03-30
