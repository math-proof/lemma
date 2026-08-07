import Lemma.Bool.Cast.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqPermute
import Lemma.List.GetPermute__Neg.eq.Get_0.of.Gt
import Lemma.List.Permute__Neg.eq.Append_AppendRotateDropTake
import Lemma.List.Permute__Neg.eq.Cons_EraseIdx
import Lemma.List.Rotate_SubLength_1.eq.Cons_DropLast.of.GtLength_0
import Lemma.Nat.ToNatSub_Neg.eq.Add_1
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetPermute__Neg.as.Permute__Neg_Get.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.MapData.eq.DataMap
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteTailMap.eq.MapPermuteTail
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermute
import Lemma.Tensor.SEqPermuteS.of.SEq.Eq.Eq.GtLength
import Lemma.Tensor.TensorMap.eq.MapTensor
import Lemma.Vector.FlattenMap.eq.MapFlatten
import Lemma.Vector.MapCast.as.Map.of.Eq
import Lemma.Vector.SplitAtMap.eq.MapSplitAt
open Bool List Nat Tensor Vector


@[main, comm]
private lemma main
  {i d : ℕ}
-- given
  (h_i : i + d < s.length)
  (X : Tensor α s)
  (f : α → β) :
-- imply
  (X.map f).permute ⟨i + d, h_i⟩ (-d) ≃ (X.permute ⟨i + d, h_i⟩ (-d)).map f := by
-- proof
  induction i generalizing s X d with
  | zero =>
    have h_toNat := ToNatSub_Neg.eq.Add_1 d
    rw [@Tensor.Permute.eq.Ite]
    simp
    have h_min : (d + 1) ⊓ s.length - 1 = d := by omega
    split_ifs with h_d h_d_neg h_d_end
    ·
      subst h_d
      have h_X_map := SEqPermute (i := ⟨0, h_i⟩) (s := s) (α := β) (X.map f)
      have h_s := Eq_Permute ⟨0, h_i⟩
      exact h_X_map.trans (SEq.symm (MapCast.as.Map.of.Eq h_s (X := X) (f := f)))
    ·
      omega
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      have h_permute : s.take (s.length - (1 - -(d : ℤ)).toNat) ++ (s.drop (s.length - (1 - -(d : ℤ)).toNat)).rotate ((1 - -(d : ℤ)).toNat ⊓ s.length - 1) = s.permute ⟨0 + d, h_i⟩ (-(d : ℤ)) := by
        simp only [h_toNat]
        simp [h_min]
        rw [Permute__Neg.eq.Cons_EraseIdx]
        simp [show (s.length - (d + 1)) = 0 by omega]
        simp [h_d_end]
        apply Rotate_SubLength_1.eq.Cons_DropLast.of.GtLength_0
        omega
      apply SEq.of.Eq
      rw [MapCast.eq.Cast_Map.of.Eq h_permute]
      rw [PermuteTailMap.eq.MapPermuteTail]
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      apply SEq.of.Eq
      apply Eq.of.EqDataS
      simp [Tensor.map]
      apply EqCast.of.SEq.Eq
      ·
        simp only [h_toNat]
        simp [Permute__Neg.eq.Append_AppendRotateDropTake, h_min]
      ·
        rw [SplitAtMap.eq.MapSplitAt]
        rw [TensorMap.eq.MapTensor]
        rw [PermuteTailMap.eq.MapPermuteTail]
        rw [DataMap.eq.MapData]
        rw [FlattenMap.eq.MapFlatten]
        symm
        apply Vector.MapCast.as.Map.of.Eq
        simp only [h_toNat]
        simp [Permute__Neg.eq.Append_AppendRotateDropTake, h_min]
  | succ i ih =>
    apply SEq.of.Eq
    apply Eq.of.All_EqGetS.GtLength_0 (h := by simp; omega)
    intro t
    have h_t := t.isLt
    simp [GetPermute__Neg.eq.Get_0.of.Gt (by simp) (d := d) (s := s) (i := ⟨i + 1 + d, h_i⟩)] at h_t
    have h_all := GetPermute__Neg.as.Permute__Neg_Get.of.GtGet_0.LtAdd_1Length (s := s) (i := i + d) (k := t) (by grind) h_t (d := d) (α := α) (by grind)
    have h_X := h_all X
    have := SEqPermuteS.of.SEq.Eq.Eq.GtLength (s := s) (i := i + d + 1) (i' := i + 1 + d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := X)
    have := SEqGetS.of.SEq.GtLength.fin (i := t) (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp)]) this
    have h_X := this.symm.trans h_X
    have h_X_map := GetPermute__Neg.as.Permute__Neg_Get.of.GtGet_0.LtAdd_1Length (s := s) (i := i + d) (k := t) (by grind) h_t (d := d) (α := β) (by grind) (X.map f)
    have := SEqPermuteS.of.SEq.Eq.Eq.GtLength (s := s) (i := i + d + 1) (i' := i + 1 + d) (d := -d) (d' := -d) (by omega) (by omega) (by omega) (by rfl) (A := X.map f)
    have := SEqGetS.of.SEq.GtLength.fin (i := t) (by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp)]) this
    have h_X_map := this.symm.trans h_X_map
    apply Eq.of.SEq
    refine h_X_map.trans ?_
    conv_lhs => erw [GetMap.eq.MapGet.fin (i := ⟨t, by grind⟩)]
    refine (ih (s := s.tail) (by grind) (X.get ⟨t, by grind⟩)).trans ?_
    conv_rhs => erw [GetMap.eq.MapGet.fin (i := ⟨t, by grind⟩)]
    conv_lhs => rw [← SEq.cast h_X]
    apply MapCast.as.Map.of.Eq h_X.1


-- created on 2026-08-07
