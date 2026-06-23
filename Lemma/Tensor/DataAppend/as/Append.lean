import Lemma.Bool.SEq.is.EqCast.of.Eq
import sympy.tensor.Basic
open Bool


@[main, cast]
private lemma main
-- given
  (A : Tensor α (m :: s))
  (B : Tensor α (n :: s)) :
-- imply
  (A ++ B).data ≃ A.data ++ B.data := by
-- proof
  apply SEq.of.Eq_Cast
  .
    simp [HAppend.hAppend]
  .
    simp [right_distrib]


-- created on 2026-05-02
