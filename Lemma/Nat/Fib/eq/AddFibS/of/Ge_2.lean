import Lemma.Nat.Add
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≥ 2) :
-- imply
  fib n = fib (n - 1) + fib (n - 2) := by
-- proof
  match n with
  | 0 =>
    contradiction
  | 1 =>
    contradiction
  | n + 2 =>
    simp
    rw [Nat.fib_add_two]
    rw [Add.comm]


-- created on 2025-10-12
