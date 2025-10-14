import stdlib.SEq
import Lemma.List.LengthPermute.eq.Length
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Bool.SEqCast.of.SEq.Eq.Eq
import Lemma.List.EqPermutePermute.of.In_Ioo_Length
import Lemma.List.TakePermute.eq.Take
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.Nat.EqMinSub
import Lemma.List.RotateDropPermute.eq.Drop
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.OfNat.eq.Cast
import Lemma.Int.EqToNat
import Lemma.Nat.SubSub
open List Tensor Bool Nat Int


@[main]
private lemma main
  {s : List ℕ}
-- given
  (h_j : j < s.length)
  (h : i < j)
  (X : Tensor α s) :
-- imply
  let d := j - i
  (X.permute ⟨i, by linarith⟩ d).permute ⟨j, by simpa [LengthPermute.eq.Length]⟩ (-d) ≃ X := by
-- proof
  intro d
  rw [Permute.eq.Ite (d := ⟨j, by simpa [LengthPermute.eq.Length]⟩) (k := -d)]
  split_ifs with h_sub h_pos h_j_0 h_j_length
  ·
    omega
  ·
    omega
  ·
    omega
  ·
    simp [LengthPermute.eq.Length] at h_j_length
    subst h_j_length
    simp
    apply SEqCast.of.SEq.Eq.Eq
    ·
      rw [EqPermutePermute.of.In_Ioo_Length ⟨h, h_j⟩]
      simp [LengthPermute.eq.Length]
      rw [(show (1 + d : ℤ).toNat = s.length - i by omega)]
      rw [EqSub_Sub.of.Gt (by linarith)]
      rw [EqMinSub]
      rw [(show (d : ℤ) = (s.length - i - 1 : ℕ) by omega)]
      rw [TakePermute.eq.Take ⟨i, by linarith⟩ (s.length - i - 1)]
      simp [RotateDropPermute.eq.Drop (i := ⟨i, by linarith⟩)]
    ·
      rw [EqPermutePermute.of.In_Ioo_Length ⟨by omega, by omega⟩]
    ·
      simp at h_sub
      simp at h_j_length
      rw [Sub_Neg.eq.Add]
      have := AddCoeS.eq.CoeAdd (α := ℤ) 1 d
      rw [Cast.eq.OfNat] at this
      rw [this]
      rw [EqToNat]
      rw [Permute.eq.Ite (d := ⟨i, by linarith⟩) (k := ↑d)]
      simp
      split_ifs with h_pos? h_i_0 h_i_length
      ·
        subst d
        subst h_i_0
        simp
        rw [EqAdd_Sub.of.Ge (by linarith)]
        -- rw [EqAddSub.of.Ge (by linarith)]
        sorry
      ·
        sorry
      ·
        omega
      ·
        omega
  ·
    simp
    sorry


-- created on 2025-10-12
-- updated on 2025-10-14
