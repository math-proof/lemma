import Lemma.Nat.DivDiv.eq.Div_Mul
import Lemma.Nat.DivMod_Mul.eq.ModDiv
import Lemma.Nat.EqAddMulDiv
open Nat


@[main]
private lemma main
-- given
  (t m n : ℕ) :
-- imply
  t / n = t / (m * n) * m + t % (m * n) / n := by
-- proof
  rw [DivMod_Mul.eq.ModDiv.comm]
  rw [Div_Mul.eq.DivDiv.comm]
  rw [EqAddMulDiv]


-- created on 2025-11-30
