import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetDot.eq.DotGet.of.Ge
import Lemma.Tensor.GetDot.eq.DotGet.of.Lt
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open List Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α [n, k])
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) = X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.eq.DotGet.of.Lt h_n
  else
    apply GetDot.eq.DotGet.of.Ge (by omega)


-- created on 2026-01-05
-- updated on 2026-01-13
