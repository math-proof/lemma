import Lemma.Algebra.Gt_0.of.Ne_0
import Lemma.Nat.LtMod.of.Gt_0
open Algebra Nat


@[main]
private lemma main
  {d : ℕ}
-- given
  (h : d ≠ 0)
  (n : ℕ) :
-- imply
  n % d < d := by
-- proof
  apply LtMod.of.Gt_0
  apply Gt_0.of.Ne_0 h


-- created on 2025-07-07
