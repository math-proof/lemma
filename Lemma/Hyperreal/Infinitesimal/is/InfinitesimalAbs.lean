import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqAbs.is.Ge_0
open Int Hyperreal


@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x → 0 ↔ |x| → 0 := by
-- proof
  if h : x ≥ 0 then
    rw [EqAbs.of.Ge_0 h]
  else
    rw [Abs.eq.Neg.of.Lt_0 (by linarith)]
    rw [InfinitesimalNeg.is.Infinitesimal]


-- created on 2025-12-20
