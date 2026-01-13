import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetDot.as.DotGet.of.Ge
import Lemma.Tensor.GetDot.as.DotGet.of.Lt
import Lemma.Tensor.GtLengthDot.of.LeLengthS.Ne_Nil
open Tensor List


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n', k'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by apply GeLength_1.of.Ne_Nil (by simp)) X Y i) ≃ X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.as.DotGet.of.Lt h_n
  else
    apply GetDot.as.DotGet.of.Ge (by omega)


-- created on 2026-01-13
