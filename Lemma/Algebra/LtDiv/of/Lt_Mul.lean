import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma left
  {k n m : ℕ}
-- given
  (h : k < n * m) :
-- imply
  k / n < m :=
-- proof
  Nat.div_lt_of_lt_mul h


@[main]
private lemma main
  {k n m : ℕ}
-- given
  (h : k < m * n) :
-- imply
  k / n < m := by
-- proof
  apply left
  rwa [Mul.comm]


-- created on 2025-05-29
-- updated on 2025-07-08
