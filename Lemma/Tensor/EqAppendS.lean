import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Fin.Eq_0
import Lemma.Tensor.DataAppend.eq.Cast_AppendDataS
import Lemma.Tensor.DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.EqHeadSplitAt_0
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
import Lemma.Vector.GetMap₂.eq.BFnGetS
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Bool Fin Tensor Vector


@[main]
private lemma main
-- given
  (A : Tensor α ([] ++ m :: s))
  (B : Tensor α ([] ++ n :: s)) :
-- imply
  let A' : Tensor α (m :: s) := A
  let B' : Tensor α (n :: s) := B
  A ++ B = A' ++ B' := by
-- proof
  intro A' B'
  simp [A', B']
  apply Eq.of.EqDataS
  rw [DataAppend.eq.Cast_AppendDataS]
  apply Eq_Cast.of.SEq
  rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
  apply SEqCast.of.SEq.Eq (by grind)
  apply SEq.of.All_EqGetS.Eq.fin (by grind)
  intro t
  simp
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  rw [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]
  have h_q := Eq_0 q
  simp [h_q] at h_qr
  simp only [h_q]
  rw [GetMap₂.eq.BFnGetS.fin]
  simp [h_qr]
  congr <;>
    apply EqHeadSplitAt_0


-- created on 2026-06-11
