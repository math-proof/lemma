import Lemma.Algebra.Ne_0.of.NeMod_0
import Lemma.Algebra.Gt_0.of.Ne_0
open Algebra


@[main]
private lemma main
  {n d : ℕ}
-- given
  (h : n % d ≠ 0) :
-- imply
  n > 0 := by
-- proof
  have h := Ne_0.of.NeMod_0 h
  apply Gt_0.of.Ne_0 h


-- created on 2025-06-16
