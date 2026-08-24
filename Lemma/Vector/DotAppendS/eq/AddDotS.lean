import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.MulAppendS.eq.AppendMulS
import Lemma.Vector.SumAppend.eq.AddSumS
open Vector


@[main, comm]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A C : List.Vector α n)
  (B D : List.Vector α m) :
-- imply
  (A ++ B) @ (C ++ D) = A @ C + B @ D := by
-- proof
  rw [Dot.eq.SumMul]
  rw [Dot.eq.SumMul A C]
  rw [Dot.eq.SumMul B D]
  rw [MulAppendS.eq.AppendMulS]
  rw [SumAppend.eq.AddSumS]


-- created on 2026-08-24
