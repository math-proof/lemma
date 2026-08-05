import Lemma.Nat.Mul_Div.ge.SubAdd_1.of.Gt_0
import Lemma.Int.FDiv.eq.Div.of.Ge_0
open Int Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d > 0) :
-- imply
  d * (n // d) ≥ n + 1 - d := by
-- proof
  rw [FDiv.eq.Div.of.Ge_0 (show 0 ≤ d by omega)]
  exact Nat.Mul_Div.ge.SubAdd_1.of.Gt_0 h


-- created on 2026-08-04
