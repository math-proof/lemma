import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Rat.Div.eq.Mul_Inv
open Rat Nat


@[main, comm]
private lemma main
  [DivisionRing α]
  {b : α}
-- given
  (h : b ≠ 0)
  (x a : α) :
-- imply
  x + a / b = (x * b + a) / b := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [MulAdd.eq.AddMulS]
  simp [h]


-- created on 2025-12-09
