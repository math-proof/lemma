import Lemma.Bool.SEq.is.SEqCast.of.Eq
import sympy.tensor.Basic
open Bool


@[main, comm]
private lemma main
-- given
  (A : Tensor α (m :: s))
  (B : Tensor α (n :: s)) :
-- imply
  (A ++ B).data ≃ A.data ++ B.data := by
-- proof
  conv_lhs => simp [HAppend.hAppend]
  unfold Tensor.append
  simp
  apply SEqCast.of.SEq.Eq
  ·
    grind
  ·
    rfl


-- created on 2026-01-10
