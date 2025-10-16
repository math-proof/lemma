import Lemma.Int.Div.eq.CeilDiv.of.Lt_0
import Lemma.Algebra.Div.eq.FloorDiv.of.Ge_0
open Algebra Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n / d =
    if d < 0 then
      ⌈n / (d : ℚ)⌉
    else
      ⌊n / (d : ℚ)⌋ := by
-- proof
  split_ifs with h
  ·
    apply Div.eq.CeilDiv.of.Lt_0 (n := n) h
  ·
    simp at h
    apply Div.eq.FloorDiv.of.Ge_0 h


-- created on 2025-03-16
-- updated on 2025-03-30
