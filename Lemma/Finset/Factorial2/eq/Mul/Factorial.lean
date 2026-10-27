import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Nat


@[path]
private lemma main
  {n : ℕ} :
-- imply
  (n * 2) ‼ = n ! * 2 ^ n := by
-- proof
  rw [mul_comm n 2, Nat.doubleFactorial_two_mul, mul_comm]


-- created on 2023-06-03
