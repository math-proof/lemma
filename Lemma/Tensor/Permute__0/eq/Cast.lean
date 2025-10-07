import sympy.tensor.tensor
import Lemma.Tensor.EqPermute__0
import Lemma.List.EqPermute__0
import Lemma.Bool.EqCast.of.SEq
open Tensor List Bool


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin s.length) :
-- imply
  X.permute i 0 = cast (by rw [EqPermute__0 i]) X := by
-- proof
  apply Eq_Cast.of.SEq
  apply EqPermute__0 X


-- created on 2025-07-14
