import Lemma.Logic.EqUFnS.of.Eq
import Lemma.Algebra.ValAppend.eq.AppendValS
import Lemma.Algebra.LengthAppend.eq.AddLengthS
import Lemma.Algebra.EqGetS.of.Eq.Lt_Length
import Lemma.Algebra.GetAppend.eq.Get.of.Lt_Length
open Algebra Logic


@[main]
private lemma main
  {a : List.Vector α N}
  {b : List.Vector α m}
  {c : List.Vector α n}
-- given
  (h₀ : i < N)
  (h₁ : i < m)
  (h₂ : a.val = (b ++ c).val) :
-- imply
  a[i] = b[i] := by
-- proof
  have h_a_length : a.val.length = N := by simp
  have h_b_length : b.val.length = m := by simp
  have h_c_length : c.val.length = n := by simp
  rw [ValAppend.eq.AppendValS] at h₂
  have h_a_length := EqUFnS.of.Eq h₂ List.length
  rw [LengthAppend.eq.AddLengthS] at h_a_length
  rw [h_b_length, h_c_length] at h_a_length
  have h_a_length : i < a.val.length := by
    rw [h_a_length]
    linarith
  have h_Eq := EqGetS.of.Eq.Lt_Length h_a_length h₂
  simp [ValAppend.eq.AppendValS] at h_Eq
  rw [GetAppend.eq.Get.of.Lt_Length (by simp_all)] at h_Eq
  simp [GetElem.getElem]
  simp [List.Vector.get]
  assumption


-- created on 2025-05-31
