import Lemma.Nat.Mul
import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Tensor.Sum.of.Eq
open Nat Tensor


@[main]
private lemma Comm
  [CommMagma α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [n]) :
-- imply
  X @ Y = Y @ X := by
-- proof
  rw [Dot.eq.SumMul__0]
  rw [Dot.eq.SumMul__0]
  apply Sum.of.Eq
  apply Mul.comm


-- created on 2026-07-21
