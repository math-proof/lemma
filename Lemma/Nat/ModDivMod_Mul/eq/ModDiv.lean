import Lemma.Nat.DivAddMul.eq.Add_Div.of.Ne_0
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Nat.EqModS.of.Eq
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Nat


@[main]
private lemma main
-- given
  (n k d : ℕ) :
-- imply
  n % (d * k) / k % d = n / k % d := by
-- proof
  if h_k : k = 0 then
    subst h_k
    simp
  else
    have := EqAddMulDiv n (k * d)
    have := EqDivS.of.Eq this k
    rw [Mul.comm (a := k)] at this
    rw [Mul_Mul.eq.MulMul] at this
    rw [DivAddMul.eq.Add_Div.of.Ne_0 h_k] at this
    have := EqModS.of.Eq this d
    simp at this
    assumption


@[main]
private lemma comm'
-- given
  (n k d : ℕ) :
-- imply
  n % (k * d) / k % d = n / k % d := by
-- proof
  rw [← main n k d]
  rw [Mul.comm]


-- created on 2025-11-16
