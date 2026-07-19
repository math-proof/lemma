import Lemma.Tensor.SEqPermute
import sympy.tensor.tensor
open Tensor


@[main, comm, cast]
private lemma main
-- given
  (h : n = 0)
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.permute i n ≃ X :=
-- proof
  h.symm.subst (motive := fun n => X.permute i n ≃ X) (SEqPermute X i)


-- created on 2026-07-11
