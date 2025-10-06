import Lemma.Tensor.LengthRepeat.eq.Get_0.of.GtVal_0
import Lemma.Algebra.LtSubS.of.Lt.Le
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.GetSet.eq.Get.of.Gt.Lt_Length
import Lemma.Algebra.Gt_0
import Lemma.Algebra.LtVal
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Tensor.GetToVector.eq.Get.of.GtLength_0
open Tensor Algebra List


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h : d.val > 0)
  (X : Tensor α s)
  (n : ℕ) :
-- imply
  let s₀ := (s.set d (n * s[d])).headD 1
  have h_s := Gt_0 d
  have h_s₀ : s₀ = s.headD 1 := by
    simp only [s₀]
    repeat rw [HeadD.eq.Get_0.of.GtLength_0]
    apply GetSet.eq.Get.of.Gt.Lt_Length h_s h
  have h_head := HeadD.eq.Get_0.of.GtLength_0 h_s 1
  have h_d_1 : d - 1 < s.tail.length := by
    simp
    apply LtSubS.of.Lt.Le (by linarith) (by simp)
  (X.repeat n d).toVector = (List.Vector.range s₀).map fun i =>
    have h_i := LtVal i
    have : i < (X.repeat n d).length := by
      simp_all [LengthRepeat.eq.Get_0.of.GtVal_0 h]
    have h_i : i < X.length := by
      rw [Length.eq.Get_0.of.GtLength_0]
      simp_all
      assumption
  cast
      (by
        congr
        simp
        congr
        repeat apply EqAddSub.of.Ge (by linarith)
      )
      ((X.get ⟨i, h_i⟩).repeat n ⟨d - 1, h_d_1⟩) := by
-- proof
  intro s₀ h_s h_s₀ h_head h_d_1
  ext i
  simp
  rw [GetToVector.eq.Get.of.GtLength_0.headd (by simpa)]
  sorry


-- created on 2025-10-05
-- updated on 2025-10-06
