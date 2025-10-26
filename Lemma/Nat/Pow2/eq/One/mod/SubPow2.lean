import sympy.core.relational
import Lemma.Nat.Pow2.ge.One
import Lemma.Nat.ModEq_Add
import Lemma.Nat.EqAddSub.of.Ge
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
-- proof
  have h_Ge_1 := Pow2.ge.One (n := n)
  denote h_eq_k : k = 2 ^ n
  rw [← h_eq_k] at ⊢ h_Ge_1
  have := ModEq_Add (n := k - 1) (k := 1)
  rwa [EqAddSub.of.Ge h_Ge_1] at this


-- created on 2025-03-15
