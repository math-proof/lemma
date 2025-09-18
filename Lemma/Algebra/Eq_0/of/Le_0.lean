import Lemma.Algebra.Ge_0
import Lemma.Algebra.Eq.of.Ge.Le
open Algebra


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≤ 0) :
-- imply
  n = 0 := by
-- proof
  have := Ge_0.nat n
  apply Eq.of.Ge.Le this h


-- created on 2025-04-12
