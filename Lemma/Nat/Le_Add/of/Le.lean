import Lemma.Nat.Le.of.Le.Le
open Nat


@[main]
private lemma main
  {x y : ℕ}
-- given
  (h : x ≤ y)
  (n : ℕ) :
-- imply
  x ≤ n + y := by
-- proof
  apply Le.of.Le.Le h (by simp)


-- created on 2025-05-04
-- updated on 2025-10-16
