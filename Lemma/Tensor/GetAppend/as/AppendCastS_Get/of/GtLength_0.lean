import Lemma.List.EqGetCons
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Tensor.GetToVector.eq.Get
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.GtLength_0
open Tensor List


@[main, fin]
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
  simp [HAppend.hAppend]
  induction b with
  | nil =>
    contradiction
  | cons b₀ b ih =>
    simp_all
    have h_i := i.isLt
    simp only [EqGetCons] at h_i
    unfold Tensor.batch_append
    simp [Tensor.batch_append]
    have := GetFromVector.eq.Get.fin (Vector.map₂ batch_append A.toVector B.toVector) ⟨i, by grind⟩
    simp at this
    rw [this]
    have := GetToVector.eq.Get.fin A i
    simp at this
    rw [this]
    have := GetToVector.eq.Get.fin B i
    simp at this
    rw [this]
    match b with
    | [] =>
      simp
      unfold Tensor.batch_append
      rfl
    | b₁ :: b =>
      simp_all
      have ih := ih (A.get i) (B.get i)
      apply SEq.of.All_SEqGetS.Eq.GtLength_0
      ·
        simp
        intro t
        have h_t := t.isLt
        simp only [Append.append] at h_t
        simp only [List.append] at h_t
        simp only [List.tail] at h_t
        simp only [EqGetCons] at h_t
        have ih := ih ⟨t, h_t⟩
        simp at ih
        have := GetFromVector.eq.Get.fin (Vector.map₂ batch_append (A.get i).toVector (B.get i).toVector) ⟨t, by simpa⟩
        simp at this
        rwa [this]
      repeat simp [Append.append]


-- created on 2026-01-10
