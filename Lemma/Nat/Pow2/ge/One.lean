import Lemma.Algebra.Pow2.gt.Zero
import Lemma.Nat.Ge_Add_1.of.Gt
import Lemma.Algebra.EqAdd0
open Algebra Nat


@[main]
private lemma main
  {n : ℕ} :
-- imply
  2 ^ n ≥ 1 := by
-- proof
  have := Pow2.gt.Zero (n := n)
  have := Ge_Add_1.of.Gt this
  rwa [EqAdd0] at this


-- created on 2025-03-15
