import Lemma.Algebra.Gt_0.of.Ne_0
import Lemma.Algebra.Div.eq.FloorDiv.of.Gt_0
open Algebra


@[main]
private lemma main
  {n d : ℕ} :
-- imply
  (n / d :ℕ) = ⌊n / (d : ℚ)⌋ := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
  ·
    have := Gt_0.of.Ne_0 h_d
    apply Div.eq.FloorDiv.of.Gt_0.nat this


-- created on 2025-07-06
