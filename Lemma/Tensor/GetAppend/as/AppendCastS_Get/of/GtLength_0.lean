import Lemma.List.EqGetCons
import Lemma.Tensor.DataAppend.as.FromVectorMap₂_CastS_ToVector.of.GtLength_0
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
open Tensor List


@[main, fin, cast, cast.fin]
private lemma main
-- given
  (h : b.length > 0)
  (A : Tensor α (b ++ m :: s))
  (B : Tensor α (b ++ n :: s))
  (i : Fin b[0]) :
-- imply
  have : i < A.length := by simp_all [Length.eq.Get_0.of.GtLength_0]
  have : i < B.length := by simp_all [Length.eq.Get_0.of.GtLength_0]
  have h_s : (b ++ m :: s).tail = b.tail ++ m :: s := by grind
  have h_s' : (b ++ n :: s).tail = b.tail ++ n :: s := by grind
  (A ++ B)[i]'(by simp_all [Length.eq.Get_0.of.GtLength_0]) ≃ cast (congrArg (Tensor α) h_s) A[i] ++ cast (congrArg (Tensor α) h_s') B[i] := by
-- proof
  simp only [GetElem.getElem]
  cases b with
  | nil =>
    contradiction
  | cons b₀ b =>
    rw [DataAppend.eq.Cast_FromVectorMap₂_CastS_ToVector.of.GtLength_0 (by grind)]
    simp
    let A' : List.Vector (Tensor α (b ++ m :: s)) ((b₀ :: b ++ m :: s).headD 1) := A.toVector
    let B' : List.Vector (Tensor α (b ++ n :: s)) ((b₀ :: b ++ n :: s).headD 1) := B.toVector
    rw [GetFromVector.eq.Get.fin (Vector.map₂ HAppend.hAppend A' B')]
    simp [A', B']
    have := GetToVector.eq.Get.fin A i
    simp at this
    rw [this]
    have := GetToVector.eq.Get.fin B i
    simp at this
    rw [this]


-- created on 2026-01-10
