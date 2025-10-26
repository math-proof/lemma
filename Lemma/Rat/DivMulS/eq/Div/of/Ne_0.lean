import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Rat.Div.eq.Mul_Inv
open Nat Rat


@[main]
private lemma main
  [DivisionRing α]
  {n d a : α}
-- given
  (h : a ≠ 0) :
-- imply
  (n * a) / (d * a) = n / d := by
-- proof
  -- Step 1: Express division as multiplication by the inverse
  rw [Div.eq.Mul_Inv]
  -- Step 2: Apply the inverse of a product and use commutativity
  rw [mul_inv_rev]
  rw [MulMul.eq.Mul_Mul]
  rw [Mul_Mul.eq.MulMul (a := a)]
  simp [h]
  rw [Div.eq.Mul_Inv]


-- created on 2025-04-06
-- updated on 2025-10-04
