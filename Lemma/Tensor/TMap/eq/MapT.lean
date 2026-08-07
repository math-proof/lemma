import Lemma.Bool.Cast.of.SEq.Eq
import Lemma.Bool.SEq.is.Eq
import Lemma.List.Swap.eq.Permute__Neg1.of.GtLength
import Lemma.Nat.AddSub.eq.Sub_Sub.of.Ge.Ge
import Lemma.Tensor.MapCast.as.Map.of.Eq
import Lemma.Tensor.PermuteMap.eq.MapPermute
import Lemma.Tensor.SEqT.of.LeLength_1
import Lemma.Tensor.T.as.Permute__Neg1.of.GtLength_0
open Bool List Nat Tensor


@[main]
private lemma main
  {f : α → β}
-- given
  (X : Tensor α s) :
-- imply
  (X.map f)ᵀ = Xᵀ.map f := by
-- proof
  if h : s.length ≥ 2 then
    rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
    conv_rhs => rw [T.eq.Cast_Permute__Neg1.of.GtLength_0 (by grind)]
    have h_permute := Permute__Neg1.eq.Swap.of.GtLength (by simp; grind) (i := s.length - 2) (s := s)
    simp [AddSub.eq.Sub_Sub.of.Ge.Ge h (show 2 ≥ 1 by grind)] at h_permute
    rw [MapCast.eq.Cast_Map.of.Eq (by rw [← h_permute])]
    apply Cast.of.SEq.Eq h_permute
    apply PermuteMap.eq.MapPermute
  else
    have h_len : s.length ≤ 1 := by omega
    have h_T := SEqT.of.LeLength_1 h_len X
    have h_T_map := SEqT.of.LeLength_1 h_len (X.map f)
    apply Eq.of.SEq
    apply h_T_map.trans
    symm
    simpa [SEq.cast h_T.symm] using MapCast.as.Map.of.Eq h_T.symm.1 (X := X) (f := f)


-- created on 2026-08-07
