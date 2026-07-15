import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.Sum.eq.Zero
open Vector


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (x y : List.Vector α 0) :
-- imply
  x @ y = 0 := by
-- proof
  rw [Dot.eq.SumMul]
  apply Sum.eq.Zero


-- created on 2024-07-01
-- updated on 2026-07-10
