import Lemma.Vector.Dot.eq.SumMul
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
  repeat rw [Dot.eq.SumMul]
  rw [Eq_Cons_Tail.head x, Eq_Cons_Tail.head y]
  rfl


-- created on 2026-07-15
