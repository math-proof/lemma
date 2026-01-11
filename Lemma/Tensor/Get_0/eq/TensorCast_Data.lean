import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Tensor.DataGet.eq.GetUnflattenData
import Lemma.Tensor.Eq.is.EqDataS
import sympy.tensor.tensor
open Bool Tensor Vector


@[main]
private lemma main
-- given
  (X : Tensor α (1 :: s)) :
-- imply
  X.get (0 : Fin 1) = ⟨cast (congrArg (List.Vector α) (by simp)) X.data⟩ := by
-- proof
  apply Eq.of.EqDataS
  simp
  apply Eq_Cast.of.SEq
  rw [DataGet.eq.GetUnflattenData.fin]
  apply SEq.of.All_EqGetS.Eq.fin
  .
    intro t
    rw [GetUnflatten.eq.Get_AddMul.fin]
    simp
  .
    simp


-- created on 2026-01-10
