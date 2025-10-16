import Lemma.Nat.LeAdd_1.of.Lt
open Nat


@[main]
private lemma main
  {n : ℕ}
  -- given
  (i : Fin n) :
-- imply
  i + 1 ≤ n := by
-- proof
  apply LeAdd_1.of.Lt
  simp


-- created on 2025-05-06
-- updated on 2025-06-18
