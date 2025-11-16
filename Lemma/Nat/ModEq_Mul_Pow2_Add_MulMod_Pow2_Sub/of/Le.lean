import Lemma.Nat.EqMulS.of.Eq
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Nat.Pow_Add.eq.MulPowS
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Nat.ModEq.of.Eq
import Lemma.Nat.ModEq_Pow2_1
import Lemma.Nat.EqMul1
import Lemma.Nat.ModEq.of.ModEq.ModEq__AddMul
import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Nat


@[main]
private lemma main
  {n m b : ℕ}
-- given
  (h : b ≤ m) :
-- imply
  n * 2 ^ b ≡ n / 2 ^ (m - b) + n % 2 ^ (m - b) * 2 ^ b [MOD 2 ^ m - 1] := by
-- proof
  have h_Eq_Add := EqAddMulDiv (n := n) (d := 2 ^ (m - b))
  have := EqMulS.of.Eq h_Eq_Add (2 ^ b)
  rw [MulAdd.eq.AddMulS] at this
  rw [MulMul.eq.Mul_Mul] at this
  rw [MulPowS.eq.Pow_Add] at this
  rw [EqAddSub.of.Ge h] at this
  have := ModEq.of.Eq this (2 ^ m - 1)
  have h_ModEq := ModEq_Pow2_1 (n := m)
  have := ModEq.of.ModEq.ModEq__AddMul h_ModEq this.symm
  grind


-- created on 2025-03-15
-- updated on 2025-03-16
