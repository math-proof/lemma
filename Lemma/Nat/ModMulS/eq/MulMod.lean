import Lemma.Nat.DivMulS.eq.Div.of.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.MulSub.eq.SubMulS
open Nat


@[main]
private lemma main
-- given
  (a b n : ℕ) :
-- imply
  (a * n) % (b * n) = a % b * n := by
-- proof
  if h : n = 0 then
    subst h
    simp
  else
    simp [mod_def]
    rw [MulMul.eq.Mul_Mul.comm]
    rw [Mul_Mul.eq.MulMul]
    rw [SubMulS.eq.MulSub]
    simp [h]
    rw [DivMulS.eq.Div.of.Ne_0 h]


-- created on 2026-07-12
