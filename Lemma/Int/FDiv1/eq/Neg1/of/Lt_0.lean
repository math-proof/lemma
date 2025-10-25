import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Int.DivInt.eq.Div
import Lemma.Rat.GeDiv.of.Le_Mul.Lt_0
import Lemma.Nat.Le_Sub_1.of.Lt
open Int Nat Rat


@[main]
private lemma main
  {d : ℤ}
-- given
  (h : d < 0) :
-- imply
  1 // d = -1 := by
-- proof
  have := LtCoeS.of.Lt (R := ℚ) h
  rw [FDiv.eq.FloorDiv]
  apply EqFloor.of.Le.Lt
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    apply GeDiv.of.Le_Mul.Lt_0
    ·
      simp
      norm_cast
      have := Le_Sub_1.of.Lt h
      simp at this
      linarith
    ·
      assumption
  ·
    simp
    norm_cast


-- created on 2025-03-30
-- updated on 2025-04-26
