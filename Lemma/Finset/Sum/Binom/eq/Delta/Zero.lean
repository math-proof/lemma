import sympy.functions.special.tensor_functions
import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * (-1) ^ k = (KroneckerDelta n 0 : ℤ) := by
-- proof
  rw [Delta.eq.Ite]
  push_cast
  rw [← Int.alternating_sum_range_choose]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _


-- created on 2023-08-19
