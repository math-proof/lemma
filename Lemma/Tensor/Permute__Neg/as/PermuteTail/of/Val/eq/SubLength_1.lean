import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Int.OfNat.eq.Cast
import Lemma.List.EqPermute__0
import Lemma.List.Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1
import Lemma.Nat.Add
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEqPermuteTail_1
open Bool Int List Nat Tensor


@[main]
private lemma main
  {s : List ℕ}
  {i : Fin s.length}
-- given
  (h : i.val = s.length - 1)
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.permute i (-d) ≃ X.permuteTail (d + 1) := by
-- proof
  rw [@Tensor.Permute.eq.Ite]
  have h_toNat := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  rw [Add.comm] at h_toNat
  simp
  split_ifs with h_d0 h_pos h_pos
  ·
    subst h_d0
    simp
    apply SEqCast.of.SEq.Eq
    ·
      rw [EqPermute__0]
    ·
      apply SEq.symm
      apply SEqPermuteTail_1
  ·
    omega
  ·
    omega
  ·
    apply SEqCast.of.SEq.Eq <;>
      rw [h_toNat]
    rw [Permute__Neg.eq.AppendTake__RotateDrop.of.Val.eq.SubLength_1 (by omega)]


-- created on 2025-12-02
