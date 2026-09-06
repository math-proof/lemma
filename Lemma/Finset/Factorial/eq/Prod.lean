import Lemma.Finset.Insert_Ico.eq.Ico_Add_1
import sympy.functions.combinatorial.factorials
import sympy.Basic
open Finset


@[main]
private lemma main
-- given
  (n : ℕ) :
-- imply
  n ! = ∏ i ∈ Finset.Ico 1 (n + 1), i := by
-- proof
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Nat.factorial_succ]
    rw [← Insert_Ico.eq.Ico_Add_1 (by omega : (1 : ℕ) ≤ n + 1)]
    rw [prod_insert (by simp [mem_Ico])]
    rw [ih]


-- created on 2020-02-23
