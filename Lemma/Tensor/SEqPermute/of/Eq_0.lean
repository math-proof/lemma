import Lemma.Tensor.SEqPermute__0
import sympy.tensor.tensor
open Tensor


@[main, comm, cast]
private lemma main
-- given
  (h_n : n = 0)
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.permute i n ≃ X := by
-- proof
  subst h_n
  apply SEqPermute__0


-- created on 2026-07-11
