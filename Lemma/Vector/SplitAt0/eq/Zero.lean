import Lemma.Vector.EqCast_0'0
import Lemma.Vector.Unflatten0.eq.Zero
open Vector


@[main]
private lemma main
  [Zero α]
-- given
  (s : List ℕ) :
-- imply
  (0 : List.Vector α s.prod).splitAt i = 0 := by
-- proof
  simp [List.Vector.splitAt]
  rw [Zero.eq.Unflatten0]
  congr
  apply EqCast_0'0
  simp


-- created on 2026-06-11
