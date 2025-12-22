import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Nat.Ne.of.Gt
import Lemma.Nat.EqDivMul.of.Ne_0
open Nat Rat


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x * y < 0)
  (h₁ : y > 0) :
-- imply
  x < 0 := by
-- proof
  have h_Ne_0 := Ne.of.Gt h₁
  have := LtDivS.of.Lt.Gt_0 h₀ h₁
  rw [EqDivMul.of.Ne_0 h_Ne_0] at this
  norm_num at this
  assumption


-- created on 2025-03-24
-- updated on 2025-04-04
