import Lemma.Set.Icc.eq.InterSingletonS.of.Ge
import Lemma.Set.Inter
open Set


@[main]
private lemma main
  [LinearOrder α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  Icc y x = {x} ∩ {y} := by
-- proof
  rw [Icc.eq.InterSingletonS.of.Ge h]
  rw [Inter.comm]


-- created on 2025-08-05
