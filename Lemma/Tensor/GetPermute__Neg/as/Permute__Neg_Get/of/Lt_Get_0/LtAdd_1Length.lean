import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Add
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthPermute__Neg.eq.Get_0.of.Gt
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Tensor.SEqPermute__0
open Bool Int Nat Tensor List


@[main]
private lemma main
  {s : List ℕ}
  {i k d : ℕ}
-- given
  (h_i : i + 1 < s.length)
  (h_k : k < s[0])
  (h_d : i ≥ d)
  (X : Tensor α s) :
-- imply
  have h_Xk : k < X.length := by rwa [Length.eq.Get_0.of.GtLength_0]
  (X.permute ⟨i + 1, h_i⟩ (-d)).get ⟨k, by rwa [LengthPermute__Neg.eq.Get_0.of.Gt (by simp; omega)]⟩ ≃ (X.get ⟨k, h_Xk⟩).permute ⟨i, by simp; omega⟩ (-d) := by
-- proof
  intro h_Xk
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  rw [Add.comm] at h_toNat
  if h_d : d = 0 then
    subst h_d
    simp
    have := SEqPermute__0 (X.get ⟨k, h_Xk⟩) ⟨i, by grind⟩
    apply SEq.symm ∘ SEq.trans this
    apply SEqGetS.of.SEq.GtLength
    apply SEq_Permute__0
  else if h_i0 : i = s.length - 2 then
    have : NeZero d := ⟨h_d⟩
    -- subst h_i0
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by grind⟩) (d := -d)]
    simp
    split_ifs with h_d0 h_pos h_pos
    ·
      omega
    ·
      omega
    ·
      apply SEq_Cast.of.SEq.Eq
      ·
        simp only [h_toNat]
        rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (by simp; omega)]
      ·
        rw [h_toNat]
        have := Permute__Neg.as.PermuteTail.of.Val.eq.SubLength_1 (by simp; omega) X (i := ⟨i + 1, h_i⟩) (d := d)
        have := Tensor.SEqGetS.of.SEq.GtLength.fin (by rwa [Tensor.LengthPermute__Neg.eq.Get_0.of.Gt (by grind)]) this (i := k)
        apply SEq.trans this
        -- simp only [show s.length - 2 + 1 = s.length - 1 by omega]
        sorry
    ·
      omega
  else
    rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := -d)]
    simp
    split_ifs with h_d0 h_pos
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        sorry
      ·
        sorry
    ·
      omega
    ·
      omega
    ·
      sorry


-- created on 2025-12-02
