import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.Mul
open Nat


@[path]
private lemma Comm
-- given
  (a b c : ℕ) :
-- imply
  a / b / c = a / c / b := by
-- proof
  repeat rw [DivDiv.eq.Div_Mul]
  rw [Mul.comm]


-- created on 2025-10-08
