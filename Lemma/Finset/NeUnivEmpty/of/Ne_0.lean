import Lemma.Finset.NeUnivEmpty.of.Gt_0
open Finset


@[main]
private lemma main
-- given
  (h : n ≠ 0) :
-- imply
  (Finset.univ : Finset (Fin n)) ≠ ∅ := by
-- proof
  apply NeUnivEmpty.of.Gt_0
  omega


-- created on 2025-12-04
