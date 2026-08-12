import Lemma.Tensor.ReshapeDiv.eq.DivReshape.of.Dvd
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X / B).unsqueeze dim = X.unsqueeze dim / B := by
-- proof
  simp only [Tensor.unsqueeze]
  apply ReshapeDiv.eq.DivReshape.of.Dvd


-- created on 2026-08-12
