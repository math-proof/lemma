import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.DataAppend.as.AppendDataS
open Bool Tensor


@[main]
private lemma main
-- given
  (A : Tensor α (m :: s))
  (B : Tensor α (n :: s)) :
-- imply
  A.data ++ B.data = cast (by grind) (A ++ B).data := by
-- proof
  apply Eq_Cast.of.SEq
  apply AppendDataS.as.DataAppend


-- created on 2026-01-10
