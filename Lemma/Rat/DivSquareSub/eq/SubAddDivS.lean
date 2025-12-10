import Lemma.Int.SquareSub.eq.SubAddSquareS_MulMul2
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivSquare.eq.Div
import Lemma.Rat.DivSub.eq.SubDivS
open Int Nat Rat


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h_a : a ≠ 0)
  (h_b : b ≠ 0) :
-- imply
  (a - b)² / (a * b) = a / b + b / a - 2 := by
-- proof
  rw [SquareSub.eq.SubAddSquareS_MulMul2]
  rw [DivSub.eq.SubDivS]
  rw [MulMul.eq.Mul_Mul]
  rw [EqDivMul.of.Ne_0]
  ·
    simp [DivAdd.eq.AddDivS]
    rw [DivSquare.eq.Div h_b]
    rw [DivSquare.eq.Div.left h_a]
  ·
    apply Mul.ne.Zero.of.Ne_0.Ne_0 h_a h_b


-- created on 2025-12-09
