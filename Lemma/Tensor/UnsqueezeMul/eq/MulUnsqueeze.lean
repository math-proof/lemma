import Lemma.Tensor.ReshapeMul.eq.MulReshape.of.Dvd
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (B : Tensor α [])
  (dim : ℕ) :
-- imply
  (X * B).unsqueeze dim = X.unsqueeze dim * B := by
-- proof
  simp only [Tensor.unsqueeze]
  apply ReshapeMul.eq.MulReshape.of.Dvd


-- created on 2026-08-15
