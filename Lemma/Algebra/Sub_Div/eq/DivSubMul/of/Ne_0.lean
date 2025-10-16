import Lemma.Algebra.Div.eq.Mul_Inv
import Lemma.Int.MulSub.eq.SubMulS
open Algebra Int


@[main]
private lemma main
  [DivisionRing α]
  {a b x : α}
-- given
  (h : b ≠ 0) :
-- imply
  x - a / b = (x * b - a) / b := by
-- proof
  repeat rw [Div.eq.Mul_Inv]
  rw [MulSub.eq.SubMulS]
  simp [h]


-- created on 2025-01-14
