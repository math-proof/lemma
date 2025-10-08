import Lemma.Nat.Eq_0.of.Le_0
import Lemma.Algebra.NotGt.is.Le
open Algebra Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : ¬n > 0) :
-- imply
  n = 0 := by
-- proof
  have h := Le.of.NotGt h
  apply Eq_0.of.Le_0 h


-- created on 2025-05-29
