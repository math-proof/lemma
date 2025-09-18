import sympy.tensor.tensor
import Lemma.Tensor.EqPermute__0
import Lemma.Algebra.EqPermute__0
import Lemma.Logic.EqCast.of.SEq
open Logic Tensor Algebra


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
