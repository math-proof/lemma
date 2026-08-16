import Lemma.Tensor.ReshapeMap.eq.MapReshape.of.Dvd
open Tensor


@[main, comm]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s)
  (dim : ℕ) :
-- imply
  (X.map f).unsqueeze dim = (X.unsqueeze dim).map f := by
-- proof
  unfold Tensor.unsqueeze
  apply ReshapeMap.eq.MapReshape.of.Dvd


-- created on 2026-08-16
