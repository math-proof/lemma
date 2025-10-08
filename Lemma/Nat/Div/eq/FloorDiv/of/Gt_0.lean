import Lemma.Int.Div.eq.FloorDiv.of.Gt_0
open Int


@[main]
private lemma main
  {n d : ℕ}
-- given
  (h : d > 0) :
-- imply
  n / d = ⌊n / (d : ℚ)⌋ := by
-- proof
  apply Div.eq.FloorDiv.of.Gt_0
  simpa


-- created on 2025-03-17
-- updated on 2025-10-08
