import Lemma.Algebra.EqMulS.of.Eq
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.Pow_Add.eq.MulPowS
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.ModEq.of.Eq
import Lemma.Algebra.Pow2.eq.One.mod.SubPow2
import Lemma.Algebra.EqMul1
import Lemma.Algebra.ModEq.of.ModEq.ModEq__AddMul
import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Nat.Mul
import Lemma.Nat.MulMul.eq.Mul_Mul
open Algebra Nat


@[main]
private lemma main
  {n m b : ℕ}
-- given
  (h : b ≤ m) :
-- imply
  n * 2 ^ b ≡ n / 2 ^ (m - b) + n % 2 ^ (m - b) * 2 ^ b [MOD 2 ^ m - 1] := by
-- proof
  have h_Eq_Add := Eq_AddMulDiv___Mod (n := n) (d := 2 ^ (m - b))
  have := EqMulS.of.Eq h_Eq_Add (2 ^ b)
  rw [MulAdd.eq.AddMulS] at this
  rw [MulMul.eq.Mul_Mul] at this
  rw [MulPowS.eq.Pow_Add] at this
  rw [EqAddSub.of.Ge h] at this
  have := ModEq.of.Eq this (2 ^ m - 1)
  have h_ModEq := Pow2.eq.One.mod.SubPow2 (n := m)
  have := ModEq.of.ModEq.ModEq__AddMul h_ModEq this
  simp at this
  assumption


-- created on 2025-03-15
-- updated on 2025-03-16
