import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
import stdlib.SEq
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_len : s'.length < s.length)
  (X : Tensor α (n :: s))
  (Y : Tensor α (n' :: s'))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by grind) (by omega) X Y i) ≃ X[i] @ Y := by
-- proof
  sorry


-- created on 2026-01-04
