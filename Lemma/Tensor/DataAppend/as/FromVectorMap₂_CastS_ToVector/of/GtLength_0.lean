import Lemma.List.Cons_Append.eq.AppendCons
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.TailAppend.eq.AppendTail.of.GtLength_0
import Lemma.Tensor.DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
open List Tensor


@[main]
private lemma main
  {b_z : List ℕ}
-- given
  (h : b_z.length > 0)
  (A : Tensor α (b_z ++ m :: s))
  (B : Tensor α (b_z ++ n :: s)) :
-- imply
  have h_tail : ∀ k, (b_z ++ k :: s).tail = b_z.tail ++ k :: s := by
    intro k
    rw [TailAppend.eq.AppendTail.of.GtLength_0 (by simpa)]
  have h_head : ∀ k, (b_z ++ k :: s).headD 1 = b_z[0] := by
    intro k
    rw [HeadD.eq.Get_0.of.GtLength_0 (by simp)]
    rw [GetAppend.eq.Get.of.GtLength (by simpa)]
  let A' : List.Vector (Tensor α (b_z.tail ++ m :: s)) b_z[0] := cast (by grind) A.toVector
  let B' : List.Vector (Tensor α (b_z.tail ++ n :: s)) b_z[0] := cast (by grind) B.toVector
  A ++ B ≃ Tensor.fromVector (List.Vector.map₂ HAppend.hAppend A' B') := by
-- proof
  intro h_tail h_head A' B'
  simp [A', B']
  apply SEq.of.SEqDataS.Eq
  ·
    rw [Cons_Append.eq.AppendCons]
    rw [EqCons_Tail.of.GtLength_0]
  ·
    rw [DataAppend.eq.Cast_FlattenMap₂_CastS_SplitAtData]
    sorry


-- created on 2026-04-25
