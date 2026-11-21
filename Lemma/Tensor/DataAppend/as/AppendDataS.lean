import Lemma.Bool.SEq.is.EqCast.of.Eq
import Instance.Data.Tensor.Defs.Part2
open Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.DataAppend.as.AppendDataS |
| comm | Tensor.AppendDataS.as.DataAppend |
| cast | Tensor.DataAppend.eq.Cast_AppendDataS |
-/
@[path, comm, cast]
private lemma main
-- given
  (A : Tensor α (m :: s))
  (B : Tensor α (n :: s)) :
-- imply
  (A ++ B).data ≃ A.data ++ B.data := by
-- proof
  apply SEq.of.Eq_Cast.Eq
  .
    simp [HAppend.hAppend]
  .
    grind


-- created on 2026-01-10
-- updated on 2026-11-20
