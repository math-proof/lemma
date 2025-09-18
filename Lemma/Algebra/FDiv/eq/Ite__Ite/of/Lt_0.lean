import Lemma.Algebra.FDiv.eq.SubNegDiv.of.Lt_0.Gt_0
import Lemma.Algebra.NotGt.is.Le
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.FDiv.eq.NegDivNeg.of.Lt_0.Lt_0
open Algebra


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n < 0) :
-- imply
  n // d =
    if d = 0 then
      0
    else if d > 0 then
      -((-n - 1) / d) - 1
    else
      -(-n / d) := by
-- proof
  split_ifs with h₀ h₁
  ·
    rw [h₀]
    simp
  ·
    apply FDiv.eq.SubNegDiv.of.Lt_0.Gt_0 h h₁
  ·
    have h₁ := Le.of.NotGt h₁
    have h_Lt := Lt.of.Le.Ne h₀ h₁
    apply FDiv.eq.NegDivNeg.of.Lt_0.Lt_0 h h_Lt


-- created on 2025-03-27
-- updated on 2025-03-30
