import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Rat.Div.eq.One.of.Gt_0
open Nat Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  (n % d : ℤ) / (d : ℚ) < 1 := by
-- proof
  have := LtMod.of.Gt_0 h n
  have : ((n % d) : ℤ) < (d : ℚ) := by
    simp [this]
  have h : (d : ℚ) > 0 := by simp [h]
  have := LtDivS.of.Lt.Gt_0 this h
  rwa [Div.eq.One.of.Gt_0 h] at this


-- created on 2025-03-20
-- updated on 2025-03-29
