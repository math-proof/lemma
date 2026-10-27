import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Nat


@[path]
private lemma main
  {n : ℕ}
-- given
  (h : n > 0) :
-- imply
  n * (n - 1) ! = n ! := by
-- proof
  exact Nat.mul_factorial_pred (by omega)


-- created on 2020-08-07
