import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.SEqToVectorS.of.SEq
open Tensor Bool


@[main]
private lemma main
-- given
  (h : n = n')
  (X : Tensor α (n :: s)) :
-- imply
  (cast (congrArg (Tensor α) (congrArg s.cons h)) X).toVector ≃ X.toVector := by
-- proof
  apply SEqToVectorS.of.SEq
  apply SEqCast.of.SEq.Eq
  ·
    simpa
  ·
    rfl


-- created on 2026-01-11
