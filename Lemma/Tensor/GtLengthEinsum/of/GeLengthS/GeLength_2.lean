import Lemma.Tensor.GtLengthDot.of.GeLengthS.GeLength_2
open Tensor


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (h : s'.length ≥ 2)
  (h_s : s.length ≥ s'.length)
  (X : Tensor α s)
  (Y : Tensor α s')
  (i : Fin s[0]) :
-- imply
  i < (X.einsum Y).length := by
-- proof
  simpa [Dot.dot] using GtLengthDot.of.GeLengthS.GeLength_2 h h_s X Y i


-- created on 2026-07-20
