import Lemma.List.EqInsertIdx.of.LtLength
import Lemma.List.InsertIdx.ne.Nil.of.Ne_Nil
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Tensor.Length.eq.Get_0.of.Ne_Nil
import Lemma.Tensor.LengthUnsqueeze.eq.Length.of.Gt_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Ne_Nil
import Lemma.Tensor.Unsqueeze.eq.TensorMap_FunGetData
import Lemma.Vector.SEq.of.All_EqGetS.Eq
open Tensor List Vector Nat


@[main]
private lemma main
  {s : List ℕ}
  {d : ℕ}
-- given
  (h_d : s.length < d)
  (X : Tensor α s) :
-- imply
  X.unsqueeze d ≃ X := by
-- proof
  induction s generalizing d with
  | nil =>
    simp at h_d
    have h_nil := EqInsertIdx.of.LtLength (by simpa) 1 (s := []) (i := d)
    constructor
    ·
      assumption
    ·
      apply HEq.of.SEqDataS.Eq
      ·
        assumption
      ·
        apply SEq.of.All_EqGetS.Eq
        ·
          intro i
          have h_i := i.isLt
          simp [h_nil] at h_i
          rw [Unsqueeze.eq.TensorMap_FunGetData]
          simp [h_i]
        ·
          rw [h_nil]
  | cons s₀ s ih =>
    apply SEq.of.All_SEqGetS.Eq.Ne_Nil
    ·
      simp [InsertIdx.ne.Nil.of.Ne_Nil]
    ·
      intro i
      have h_d_pos := Gt_0.of.Gt h_d
      have h_i := i.isLt
      simp [LengthUnsqueeze.eq.Length.of.Gt_0 h_d_pos] at h_i
      simp [Length.eq.Get_0.of.Ne_Nil] at h_i
      have := GetUnsqueeze.as.UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) h_d_pos h_i X
      apply SEq.trans this
      ·
        simp at h_d
        apply ih (by omega) (X.get ⟨i, h_i⟩)
      ·
        rw [EqInsertIdx.of.LtLength h_d]


-- created on 2025-10-10
-- updated on 2025-11-30
