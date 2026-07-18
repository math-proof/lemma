import Lemma.Tensor.GetDot.as.DotGet.of.Ge.GtLengthS
import Lemma.Tensor.GetDot.as.DotGet.of.Lt.GtLengthS
import Lemma.Tensor.GtLengthDot.of.GeLengthS
open Tensor


@[main, fin]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : s.length > s'.length)
  (X : Tensor α (n :: (s ++ [k])))
  (Y : Tensor α (s' ++ [n', k']))
  (i : Fin n) :
-- imply
  (X @ Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i] @ Y := by
-- proof
  if h : k < n' then
    apply GetDot.as.DotGet.of.Lt.GtLengthS h_s h
  else
    apply GetDot.as.DotGet.of.Ge.GtLengthS h_s (by omega)


-- created on 2026-07-18
