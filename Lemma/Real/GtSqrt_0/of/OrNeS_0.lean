import Lemma.Nat.GtAddSquareS0.of.OrNeS_0
import Lemma.Real.GtSqrt_0.of.Gt_0
open Real Nat


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≠ 0 ∨ y ≠ 0) :
-- imply
  √(x² + y²) > 0 := by
-- proof
  apply GtSqrt_0.of.Gt_0
  apply GtAddSquareS0.of.OrNeS_0 h


-- created on 2018-07-17
