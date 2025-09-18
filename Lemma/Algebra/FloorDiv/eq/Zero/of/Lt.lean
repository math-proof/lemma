import Lemma.Algebra.EqFloor.is.Le.Lt
import Lemma.Algebra.Div.ge.Zero
import Lemma.Algebra.LtDiv.of.Lt_Mul.Gt_0
open Algebra


@[main]
private lemma main
  {n k : ℕ}
-- given
  (h : k < n) :
-- imply
  ⌊(k : ℚ) / n⌋ = 0 := by
-- proof
  apply EqFloor.of.Le.Lt
  ·
    apply Div.ge.Zero
  ·
    simp
    apply LtDiv.of.Lt_Mul.Gt_0
    ·
      simpa
    ·
      simp
      linarith


-- created on 2025-07-07
