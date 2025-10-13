import Lemma.Nat.Ge_1.of.Gt_0
import Lemma.Nat.Gt_0.of.Ne_0
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h : n ≠ 0) :
-- imply
  n ≥ 1 := 
-- proof
  (Ge_1.of.Gt_0 ∘ Gt_0.of.Ne_0) h


-- created on 2025-10-13
