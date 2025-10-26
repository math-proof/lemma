import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Nat.ToNatSub_Neg.eq.Add
import Lemma.Nat.Add
import Lemma.Nat.EqSubAdd
import Lemma.Tensor.Permute.eq.Ite
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
open List Tensor Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [NeZero (i : ℕ)]
  {s : List ℕ}
-- given
  (h : i + d < s.length - 1)
  (X : Tensor α s) :
-- imply
  have h_d := NeZero.pos d
  have h_i : i + d < s.length := by omega
  (X.permute ⟨i + d, h_i⟩ (-d)).permute ⟨i, by simp; omega⟩ d ≃ X := by
-- proof
  intro h_d h_i
  have h_i_pos := NeZero.pos i
  rw [@Tensor.Permute.eq.Ite (i := ⟨i, by simp; omega⟩) (d := d)]
  simp
  have h_permute := EqPermutePermute.of.In_Ioo_Length (s := s) (i := i) (j := i + d) ⟨by omega, by omega⟩
  simp at h_permute
  rw [EqSubAdd.left] at h_permute
  have h_toNatSub := Cast.eq.OfNat (α := ℤ) 1 ▸ ToNatSub_Neg.eq.Add 1 d
  split_ifs with h_sub h_pos
  repeat omega
  apply SEq.of.SEqDataS.Eq
  ·
    sorry
  ·
    sorry


-- created on 2025-10-26
