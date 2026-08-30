import Lemma.Nat.SquareAdd.eq.AddAddSquareS_MulMul2
import Lemma.Nat.SquareMul.eq.MulSquareS
import Lemma.Nat.Eq_0.is.EqSquare_0
import Lemma.Rat.SquareDiv.eq.DivSquareS
import Lemma.Rat.EqMul.is.Eq_Div.of.Ne_0
import Lemma.Int.Sub.eq.Zero.is.Eq
import Lemma.Complex.EqSquareSqrt
open Nat Rat Int Complex


/--
| attributes | lemma |
| :---: | :---: |
| main | Complex.Eq_SquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0 |
| comm | Complex.EqSquareAddMulSqrt.of.Eq0SubSquare_MulMul4.Ne_0 |
-/
@[main, comm]
private lemma main
  {x a b c : ℂ}
-- given
  (h₀ : a ≠ 0)
  (h₁ : b² - 4 * a * c = 0) :
-- imply
  a * x² + b * x + c = (√a * x + b / (2 * √a))² := by
-- proof
  have hsqrt : √a ≠ 0 := by
    intro h
    apply h₀
    rw [← EqSquareSqrt (x := a)]
    apply EqSquare_0.of.Eq_0 h
  have hc : c = b² / (4 * a) := by
    apply Eq_Div.of.EqMul.Ne_0.left
    ·
      simp [h₀]
    apply Eq.symm
    apply Eq.of.Sub.eq.Zero h₁
  rw [hc]
  rw [SquareAdd.eq.AddAddSquareS_MulMul2]
  rw [SquareMul.eq.MulSquareS]
  rw [EqSquareSqrt]
  rw [SquareDiv.eq.DivSquareS]
  have h2 : (2 * √a)² = 4 * a := by
    rw [SquareMul.eq.MulSquareS]
    rw [EqSquareSqrt]
    norm_num
  rw [h2]
  have hcross : 2 * (√a * x) * (b / (2 * √a)) = b * x := by
    field_simp [hsqrt]
  rw [hcross]
  ring


-- created on 2018-11-12
-- updated on 2026-08-28
