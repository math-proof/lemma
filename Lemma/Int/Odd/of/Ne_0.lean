import Lemma.Bool.Cond.of.Or_Not.Cond
import Lemma.Set.Mod.In.Range.of.Gt_0
import Lemma.Set.Or_Eq.of.In_Ico
open Set


@[main]
private lemma main
  {n : ℤ}
-- given
  (h : n % 2 ≠ 0) :
-- imply
  n is odd := by
-- proof
  rw [IntegerRing.odd_iff]
  apply Bool.Cond.of.Or_Not.Cond _ h
  grind


-- created on 2026-08-08
