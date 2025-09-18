import Lemma.Algebra.MulMul.eq.Mul_Mul
import Lemma.Algebra.Div.eq.Mul_Inv
open Algebra


@[main]
private lemma main
  [Field α]
  {n d a : α}
-- given
  (h : a ≠ 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  -- Step 1: Express division as multiplication by the inverse
  rw [div_eq_mul_inv]
  -- Step 2: Apply the inverse of a product and use commutativity
  rw [mul_inv_rev]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := a)]
  simp [h]
  rw [Div.eq.Mul_Inv]


-- created on 2025-04-06
