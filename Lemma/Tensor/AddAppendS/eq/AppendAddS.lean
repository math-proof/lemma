import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.SEqBFnS.of.SEq.SEq
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.ValAppend.eq.AppendValS
import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
import Theorem.Vector.GetAdd.eq.AddGetS
open Bool Tensor Vector


private lemma appendGetRight
  {i : Fin (n + m)}
-- given
  (h₀ : (i : ℕ) ≥ n)
  (a : List.Vector α n)
  (b : List.Vector α m) :
-- imply
  (a ++ b).get i = b.get ⟨(i : ℕ) - n, by grind⟩ := by
-- proof
  have h₁ : (i : ℕ) - n < m := by
    have := h₀
    grind
  simp [List.Vector.get]
  simp [ValAppend.eq.AppendValS]
  rw [List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by grind) (by grind)]
  grind

private lemma appendData
  [Add α]
-- given
  (a c : List.Vector α n)
  (b d : List.Vector α m) :
-- imply
  a ++ b + (c ++ d) = a + c ++ (b + d) := by
-- proof
  ext i
  if h_i : n > i then
    rw [Vector.GetAdd.eq.AddGetS.fin]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [GetAppend.eq.Get.of.Lt.fin h_i]
    rw [Vector.GetAdd.eq.AddGetS.fin]
  else
    rw [Vector.GetAdd.eq.AddGetS.fin]
    rw [appendGetRight (by grind)]
    rw [appendGetRight (by grind)]
    rw [appendGetRight (by grind)]
    rw [Vector.GetAdd.eq.AddGetS.fin]

/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.AddAppendS.eq.AppendAddS |
| comm | Tensor.AppendAddS.eq.AddAppendS |
-/
@[path, comm]
private lemma main
  [Add α]
-- given
  (A C : Tensor α (n :: s))
  (B D : Tensor α (m :: s)) :
-- imply
  A ++ B + (C ++ D) = A + C ++ (B + D) := by
-- proof
  apply Eq.of.EqDataS
  apply Eq.of.SEq
  apply SEq.of.SEq.SEq (c := A.data ++ B.data + (C.data ++ D.data))
  ·
    rw [DataAdd.eq.AddDataS]
    apply SEqBFnS.of.SEq.SEq
      (DataAppend.as.AppendDataS A B)
      (DataAppend.as.AppendDataS C D)
      (fun {n} (x y : List.Vector α n) => x + y)
  ·
    rw [appendData]
    rw [← DataAdd.eq.AddDataS, ← DataAdd.eq.AddDataS]
    exact DataAppend.as.AppendDataS (A + C) (B + D)


-- created on 2018-08-04
-- updated on 2026-11-20
