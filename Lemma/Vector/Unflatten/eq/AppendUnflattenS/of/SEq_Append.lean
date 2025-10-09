import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.GetVal.eq.Get.of.Lt
import Lemma.Nat.Ge.of.NotLt
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt
import Lemma.Vector.Get_AddMul.eq.GetUnflatten.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetUnflatten.eq.Get_AddMul
import Lemma.Vector.EqGetS.of.Eq.Lt
import Lemma.Algebra.LtSub.is.Lt_Add.of.Ge
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.SubAdd.eq.AddSub.of.Le
import Lemma.Algebra.MulSub.eq.SubMulS
open Algebra Vector Nat


@[main]
private lemma main
  {v : List.Vector α ((m + n) * k)}
  {a : List.Vector α (m * k)}
  {b : List.Vector α (n * k)}
-- given
  (h : v ≃ a ++ b) :
-- imply
  v.unflatten = a.unflatten ++ b.unflatten := by
-- proof
  ext i j
  have hij := AddMul.lt.Mul i j
  have h_v := Get_AddMul.eq.GetUnflatten v i j
  simp [GetElem.getElem] at h_v
  rw [← h_v]
  simp [List.Vector.get]
  let ⟨i, h_i⟩ := i
  simp_all
  simp [List.Vector.get] at h_v
  repeat rw [GetVal.eq.Get.of.Lt (by simp_all)]
  by_cases hi : i < m
  ·
    have := GetAppend.eq.Get.of.Lt hi a.unflatten b.unflatten
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    simp [GetElem.getElem]
    simp [List.Vector.get]
    simp [this]
    have := EqGetS.of.Eq.Lt.heter (i := i * k + j) (by linarith) h
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [this]
    have h_ij := AddMul.lt.Mul.of.Lt hi j
    have := GetAppend.eq.Get.of.Lt h_ij a b
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [this]
    have := Get_AddMul.eq.GetUnflatten.of.Lt hi a j
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [this]
  ·
    have hi := Ge.of.NotLt hi
    have := GetAppend.eq.Get_Sub.of.Lt_Add.Ge hi h_i a.unflatten b.unflatten
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    simp [GetElem.getElem]
    simp [List.Vector.get]
    simp [this]
    have := EqGetS.of.Eq.Lt.heter (i := i * k + j) (by linarith) h
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [this]
    have h_ij : i * k + j ≥ m * k := by
      nlinarith
    have := GetAppend.eq.Get_Sub.of.Lt_Add.Ge h_ij (by linarith) a b
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [this]
    have h_i := LtSub.of.Lt_Add.Ge hi h_i
    rw [MulAdd.eq.AddMulS] at hij
    have hij := LtSub.of.Lt_Add.Ge (by linarith) hij
    have h_eq : i * k + j - m * k = (i - m) * k + j := by
      rw [SubAdd.eq.AddSub.of.Le (by nlinarith)]
      rw [SubMulS.eq.MulSub.nat]
    rw [h_eq] at hij
    have := Get_AddMul.eq.GetUnflatten.of.Lt h_i b
    simp [GetElem.getElem] at this
    simp [List.Vector.get] at this
    rw [← this]
    simp [h_eq]


-- created on 2025-05-31
-- updated on 2025-06-01
