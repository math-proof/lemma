import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import Lemma.Nat.LtVal
import Lemma.Tensor.EqLengthUnsqueeze_0'1
import Lemma.Nat.Eq_0.of.Lt_1
import Lemma.Nat.Eq_0.of.EqVal_0
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.List.InsertIdx.ne.Nil.of.Ne_Nil
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.List.TailInsertIdx.eq.InsertIdxTail.of.GtLength_0
import Lemma.Tensor.GetCast.eq.Cast_Get.of.Lt_Get_0.Eq.GtLength_0
open Tensor Nat List Bool


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_s : s = s')
  (h_d : d ≤ s.length)
  (X : Tensor α s) :
-- imply
  X.unsqueeze d ≃ (cast (congrArg (Tensor α) h_s) X).unsqueeze d := by
-- proof
  induction d generalizing s s' X with
  | zero =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      aesop
    ·
      intro i
      have h_i := LtVal i
      simp only [EqLengthUnsqueeze_0'1 X] at h_i
      have h_i := Eq_0.of.Lt_1 h_i
      simp [Eq_0.of.EqVal_0 h_i]
      have := EqGetUnsqueeze.fin X
      simp at this
      simp [this]
      have := EqGetUnsqueeze.fin (cast (congrArg (Tensor α) h_s) X)
      simp at this
      simp [this]
      aesop
    ·
      simp [h_s]
  | succ d ih =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      apply InsertIdx.ne.Nil.of.Ne_Nil
      aesop
    ·
      intro i
      have h_i := LtVal i
      simp [LengthUnsqueeze.eq.Length.of.Gt_0] at h_i
      rw [Length.eq.Get_0.of.GtLength h_d] at h_i
      repeat rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin]
      ·
        simp
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          apply List.InsertIdxTail.eq.TailInsertIdx.of.GtLength_0
          omega
        ·
          apply List.InsertIdxTail.eq.TailInsertIdx.of.GtLength_0
          simp [← h_s]
          omega
        ·
          rw [GetCast.eq.Cast_Get.of.Lt_Get_0.Eq.GtLength_0.fin _ h_s (by simpa)]
          have h_s := congrArg (List.tail) h_s
          apply ih h_s (by grind) (X.get ⟨i, by rwa [Tensor.Length.eq.Get_0.of.GtLength h_d]⟩)
      ·
        simp [← h_s]
        omega
      ·
        simp
      ·
        simp_all
      ·
        omega
      ·
        simp
      ·
        simp_all
    ·
      simp [h_s]


-- created on 2025-10-10
