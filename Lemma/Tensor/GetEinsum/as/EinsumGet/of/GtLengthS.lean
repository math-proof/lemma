import Lemma.Tensor.GetEinsum.as.EinsumGet.of.Ge.GtLengthS
import Lemma.Tensor.GetEinsum.as.EinsumGet.of.Lt.GtLengthS
import Lemma.Tensor.GtLengthDot.of.GeLengthS
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h_s : sₜ.length > s'ₜ.length)
  (X : Tensor α (n :: (sₐ :: sₜ ++ [k])))
  (Y : Tensor α (s'ₐ :: s'ₜ ++ [n', k']))
  (i : Fin n) :
-- imply
  (X.einsum Y)[i]'(GtLengthDot.of.GeLengthS (by grind) X Y i) ≃ X[i].einsum Y := by
-- proof
  if h : k < n' then
    apply GetEinsum.as.EinsumGet.of.Lt.GtLengthS h_s h
  else
    apply GetEinsum.as.EinsumGet.of.Ge.GtLengthS h_s (by omega)


-- created on 2026-07-18
