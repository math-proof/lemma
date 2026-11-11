import Instance.Data.Vector.Basic.Dot
import Lemma.Vector.Dot.eq.SumMul
open Vector


@[path]
private lemma main
  [Add α] [Zero α] [Mul α]
-- given
  (x y : List.Vector α (.succ n)) :
-- imply
  x ⬝ᵥ y = x.head * y.head + x.tail ⬝ᵥ y.tail := by
-- proof
  repeat rw [Dot.eq.SumMul]
  rw [Eq_Cons_Tail.head x, Eq_Cons_Tail.head y]
  rfl


-- created on 2026-07-15
