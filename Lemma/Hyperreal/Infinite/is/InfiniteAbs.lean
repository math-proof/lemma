import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqAbs.of.Ge_0
open Int Hyperreal


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinite x ↔ Infinite |x| := by
-- proof
  if h : x ≥ 0 then
    rw [EqAbs.of.Ge_0 h]
  else
    rw [Abs.eq.Neg.of.Lt_0 (by linarith)]
    rw [InfiniteNeg.is.Infinite]


-- created on 2025-12-20
