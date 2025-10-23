import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.Div.ge.Zero
import Lemma.Rat.LtDiv.of.Lt_Mul.Gt_0
import Lemma.Nat.Gt_0
open Nat Rat Int


@[main]
private lemma main
  {n : ℕ}
-- given
  (j : Fin n) :
-- imply
  ⌊(j : ℚ) / n⌋ = 0 := by
-- proof
  apply EqFloor.of.Le.Lt
  ·
    apply Div.ge.Zero
  ·
    simp
    apply LtDiv.of.Lt_Mul.Gt_0
    ·
      simp
    ·
      have := Gt_0 j
      simpa


-- created on 2025-07-06
