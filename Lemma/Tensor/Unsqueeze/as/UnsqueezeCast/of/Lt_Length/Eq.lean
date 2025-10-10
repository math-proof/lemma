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
import Lemma.Nat.EqSubAdd
open Tensor Nat List Bool


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_s : s ≠ [])
  (h : s = s')
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d ≃ (cast (congrArg (Tensor α) h) X).unsqueeze d := by
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
      have := EqGetUnsqueeze.fin (cast (congrArg (Tensor α) h) X)
      simp at this
      simp [this]
      aesop
    ·
      simp [h]
  | succ d ih =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      apply InsertIdx.ne.Nil.of.Ne_Nil h_s
    ·
      intro i
      have h_i := LtVal i
      simp [LengthUnsqueeze.eq.Length.of.Gt_0] at h_i
      rw [Length.eq.Get_0.of.Ne_Nil h_s] at h_i
      repeat rw [GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin]
      ·
        apply SEqCastS.of.SEq.Eq.Eq
        ·
          rw [EqSubAdd]
          sorry
        ·
          sorry
        ·
          sorry
      ·
        apply GtLength_0.of.Ne_Nil
        aesop
      ·
        simp
      ·
        simp_all
      ·
        apply GtLength_0.of.Ne_Nil h_s
      ·
        simp
      ·
        simp_all
    ·
      simp [h]


-- created on 2025-10-10
