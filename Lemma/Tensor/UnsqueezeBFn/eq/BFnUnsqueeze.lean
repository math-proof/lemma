import Lemma.Tensor.ReshapeBFn.eq.BFnReshape.of.Dvd
open Tensor


@[main]
private lemma main
-- given
  (f : α → α → α)
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X.map (f · B.data[0])).unsqueeze dim = (X.unsqueeze dim).map (f · B.data[0]) := by
-- proof
  simp only [Tensor.unsqueeze]
  apply ReshapeBFn.eq.BFnReshape.of.Dvd


-- created on 2026-08-16
