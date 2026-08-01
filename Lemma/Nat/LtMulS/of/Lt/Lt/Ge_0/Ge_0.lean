import Lemma.Nat.EqMul_0'0
import Lemma.Nat.Lt.of.Le.Lt
import Lemma.Nat.LtMulS.of.Lt.Lt.Gt_0.Gt_0
open Nat


@[main, comm 12]
private lemma main
  [MulZeroClass α] [LinearOrder α]
  [MulPosStrictMono α] [PosMulStrictMono α]
  {x y a b : α}
-- given
  (h_a : a ≥ 0)
  (h_x : x ≥ 0)
  (h₁ : a < b)
  (h₂ : x < y) :
-- imply
  a * x < b * y := by
-- proof
  obtain rfl | hx := eq_or_lt_of_le h_x
  ·
    rw [EqMul_0'0]
    have hb := Lt.of.Le.Lt h_a h₁
    have hy := Lt.of.Le.Lt (le_refl 0) h₂
    exact mul_pos hb hy
  ·
    apply LtMulS.of.Lt.Lt.Gt_0.Gt_0
    ·
      exact Lt.of.Le.Lt h_a h₁
    ·
      exact hx
    ·
      exact h₁
    ·
      exact h₂


-- created on 2018-07-06
