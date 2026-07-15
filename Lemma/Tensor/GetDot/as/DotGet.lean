import Lemma.List.Ne_Nil.is.GeLength_1
import Lemma.Tensor.GetDot.as.DotGet.of.Gt
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
  else if h_n : k > n' then
    apply GetDot.as.DotGet.of.Gt (by omega)
  else
    sorry


@[main, fin]
private lemma une
  [NonUnitalNonAssocSemiring α]
-- given
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α [n'])
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.LeLengthS.Ne_Nil (by simp) (by simp) X Y i) ≃ X[i] @ Y := by
-- proof
  if h_n : k < n' then
    apply GetDot.as.DotGet.of.Lt.une h_n
  else if h_n : k > n' then
    apply GetDot.as.DotGet.of.Gt.une (by omega)
  else
    sorry


-- created on 2026-01-13
