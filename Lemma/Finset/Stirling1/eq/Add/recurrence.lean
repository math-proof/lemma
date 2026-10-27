import Mathlib.Combinatorics.Enumerative.Stirling
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n k : ℕ} :
-- imply
  Nat.stirlingFirst (n + 1) (k + 1) = Nat.stirlingFirst n k + n * Nat.stirlingFirst n (k + 1) := by
-- proof
  rw [Nat.stirlingFirst_succ_succ]
  ring


-- created on 2021-07-31
