import Lemma.Vector.EqCons_Tail
open Vector


@[main]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (x y : List.Vector α (.succ n)) :
-- imply
  x @ y = x.head * y.head + x.tail @ y.tail := by
-- proof
  unfold Dot.dot
  rw [← EqCons_Tail x, ← EqCons_Tail y]
  rfl


-- created on 2026-07-15
