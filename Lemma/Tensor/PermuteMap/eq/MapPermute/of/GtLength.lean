import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.SEq.is.EqCast.of.Eq
import Lemma.List.EqPermute
import Lemma.List.GetPermute.eq.Get.of.Gt
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.Gt_0
import Lemma.Tensor.Eq.is.All_EqGetS.of.GtLength_0
import Lemma.Tensor.GetMap.eq.MapGet
import Lemma.Tensor.GetPermute.as.PermuteGet.of.GtGet_0.LtAdd_1Length
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.PermuteHeadMap.eq.MapPermuteHead
import Lemma.Tensor.SEqPermute
open Bool List Nat Tensor


@[main, comm]
private lemma main
-- given
  (h_i : s.length > i)
  (X : Tensor α s)
  (d : ℕ)
  (f : α → β) :
-- imply
  (X.map f).permute ⟨i, h_i⟩ d ≃ (X.permute ⟨i, h_i⟩ d).map f := by
-- proof
  have h_s := Gt_0 ⟨i, h_i⟩
  induction i generalizing s X d with
  | zero =>
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d h_d h_d
    ·
      subst h_d
      have h_X_map := SEqPermute (i := ⟨0, h_i⟩) (s := s) (α := β) (X.map f)
      have h_s := Eq_Permute ⟨0, h_i⟩
      exact h_X_map.trans (SEq.symm (MapCast.as.Map.of.Eq h_s (X := X) (f := f)))
    ·
      simp [@Tensor.Permute.eq.Ite]
      split_ifs
      apply SEq.of.Eq
      rw [PermuteHeadMap.eq.MapPermuteHead]
      rw [MapCast.eq.Cast_Map.of.Eq]
      rw [Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
    ·
      omega
    ·
      omega
  | succ i ih =>
    apply SEq.of.Eq
    apply Eq.of.All_EqGetS.GtLength_0 (h := by simpa)
    intro t
    have h_t := t.isLt
    simp [GetPermute.eq.Get.of.Gt (by simp) d (s := s) (i := ⟨i + 1, h_i⟩) (j := 0)] at h_t
    have h_all := GetPermute.as.PermuteGet.of.GtGet_0.LtAdd_1Length (s := s) (i := i) (k := t) h_i h_t (d := d) (α := α)
    apply Eq.of.SEq
    refine (GetPermute.as.PermuteGet.of.GtGet_0.LtAdd_1Length (s := s) (i := i) (k := t) h_i h_t (d := d) (α := β) (X.map f)).trans ?_
    conv_lhs => erw [GetMap.eq.MapGet.fin (i := ⟨t, by grind⟩)]
    refine (ih (s := s.tail) (by grind) (X.get ⟨t, by grind⟩) d (by grind)).trans ?_
    conv_rhs => erw [GetMap.eq.MapGet.fin (i := ⟨t, by grind⟩)]
    have h := h_all X
    conv_lhs => rw [← SEq.cast h]
    apply MapCast.as.Map.of.Eq h.1


-- created on 2026-08-07
