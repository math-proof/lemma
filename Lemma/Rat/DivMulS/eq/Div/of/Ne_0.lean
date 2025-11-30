import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Rat.Div.eq.Mul_Inv
open Nat Rat


@[main]
private lemma main
  [DivisionSemiring α]
  {n d a : α}
-- given
  (h : a ≠ 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  rw [Div.eq.Mul_Inv]
  rw [mul_inv_rev]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := a)]
  simp [h]
  rw [Div.eq.Mul_Inv]


-- created on 2025-04-06
-- updated on 2025-10-04
