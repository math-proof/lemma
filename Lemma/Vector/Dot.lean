import Lemma.Vector.Dot.eq.SumMul
open Vector


@[main]
private lemma Comm
  [CommMagma α] [AddCommMonoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a @ b = b @ a := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul]
  exact congrArg (·.sum) (Mul.comm a b)


-- created on 2026-07-29
