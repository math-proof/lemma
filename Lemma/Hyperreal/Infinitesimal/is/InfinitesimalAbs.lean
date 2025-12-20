import Lemma.Hyperreal.Infinitesimal.is.InfinitesimalNeg
import Lemma.Int.Abs.eq.Neg.of.Lt_0
import Lemma.Int.EqAbs.of.Ge_0
open Int Hyperreal


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  Infinitesimal x ↔ Infinitesimal |x| := by
-- proof
  if h : x ≥ 0 then
    rw [EqAbs.of.Ge_0 h]
  else
    rw [Abs.eq.Neg.of.Lt_0 (by linarith)]
    rw [InfinitesimalNeg.is.Infinitesimal]


-- created on 2025-12-20
