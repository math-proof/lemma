import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Int.Sub.eq.NegSub
open Hyperreal Int


@[main]
private lemma Comm
  {a b : ℝ*} :
-- imply
  Infinite (a - b) ↔ Infinite (b - a) := by
-- proof
  rw [Sub.eq.NegSub]
  rw [InfiniteNeg.is.Infinite]


-- created on 2025-12-20
