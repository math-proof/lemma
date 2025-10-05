import Lemma.Algebra.Gt_0
import Lemma.Algebra.Gt_0.of.Ne_0
open Algebra


@[main]
private lemma main
  {n : Fin m}
-- given
  (h : n ≠ ⟨0, Gt_0 n⟩) :
-- imply
  n.val > 0 := by
-- proof
  suffices n.val ≠ 0 by
    exact Gt_0.of.Ne_0 this
  intro hval
  apply h
  ext
  assumption


-- created on 2025-10-05
