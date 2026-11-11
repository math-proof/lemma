import Instance.Data.Vector.Basic.Dot
import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.Sum.eq.Zero
open Vector


@[path]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (x y : List.Vector α 0) :
-- imply
  x ⬝ᵥ y = 0 := by
-- proof
  rw [Dot.eq.SumMul]
  apply Sum.eq.Zero


-- created on 2024-07-01
-- updated on 2026-07-10
