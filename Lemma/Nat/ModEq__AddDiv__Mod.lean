import sympy.core.relational
import Lemma.Nat.ModEq_Pow2_1
import Lemma.Nat.ModEq.of.Eq
import Lemma.Nat.ModEq.of.ModEq.ModEq__AddMul
import Lemma.Nat.Eq_AddMulDiv___Mod
import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
  {n m : ℕ} :
-- imply
  n ≡ n / 2 ^ m + n % 2 ^ m [MOD 2 ^ m - 1] := by
-- proof
  have h_ModEq__1 := ModEq_Pow2_1 (n := m)
  denote h_eq_k : k = 2 ^ m
  rw [← h_eq_k]
  rw [← h_eq_k] at h_ModEq__1
  have h_Eq_Add := Eq_AddMulDiv___Mod (n := n) (d := k)
  have h_ModEq := ModEq.of.Eq h_Eq_Add (k - 1)
  have := ModEq.of.ModEq.ModEq__AddMul h_ModEq__1 h_ModEq
  simp at this
  assumption


-- created on 2025-03-10
-- updated on 2025-03-16
