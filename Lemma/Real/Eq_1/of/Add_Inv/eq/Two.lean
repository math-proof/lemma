import Lemma.Int.Eq_0.of.EqSquare_0
import Lemma.Int.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Int.AddSub.eq.SubAdd
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.Add_Inv.eq.DivAddMul.of.Ne_0
open Rat Nat Int


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x + x⁻¹ = 2) :
-- imply
  x = 1 := by
-- proof
  rw [Add_Inv.eq.DivAddMul.of.Ne_0 (by grind)] at h
  have h := Eq_Mul.of.EqDiv.Ne_0 (by grind) h
  rw [Mul.eq.Square] at h
  have h := Sub.eq.Zero.of.Eq h
  have h_square := SquareSub.eq.SubAddSquareS_MulMul2 x 1
  simp at h_square
  rw [← h_square] at h
  apply Eq.of.Sub.eq.Zero
  apply Eq_0.of.EqSquare_0 h


-- created on 2025-12-10
