import Lemma.Algebra.FDiv.eq.Sub_1.of.Gt_0.Lt_0
import Lemma.Algebra.FDiv.eq.NegEDivNeg.of.Le_0.Lt_0
import Lemma.Algebra.NotGt.is.Le
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n // d =
    if n > 0 then
      (n - 1) / d - 1
    else
      -(-n / d) := by
-- proof
  -- n / d here means euclidean division, ie, Int.ediv
  -- Split the proof into cases based on the sign of n
  split_ifs with h₀
  ·
    apply FDiv.eq.Sub_1.of.Gt_0.Lt_0 h₀ h
  ·
    have := Le.of.NotGt h₀
    apply FDiv.eq.NegEDivNeg.of.Le_0.Lt_0 this h


-- created on 2025-03-27
