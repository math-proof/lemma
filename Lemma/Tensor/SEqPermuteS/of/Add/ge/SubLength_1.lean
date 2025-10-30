import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
import Lemma.List.EqPermute__0
import Lemma.List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
import Lemma.List.Permute.eq.Ite
import Lemma.Nat.Eq.of.Sub.eq.Zero.Ge
import Lemma.Nat.EqSub.of.EqAdd
import Lemma.Tensor.Permute.eq.Ite
import Lemma.Tensor.SEq.is.SEqDataS.of.Eq
import stdlib.SEq
import sympy.tensor.Basic
open Bool List Nat Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {i : Fin s.length}
-- given
  (h : i + d ≥ s.length) :
-- imply
  X.permute i d ≃ X.permute i (s.length - i : ℕ) := by
-- proof
  by_cases h_d : i + d = s.length
  ·
    have h_d := Eq_Sub.of.EqAdd.left h_d
    subst h_d
    rfl
  ·
    have h_d := Gt.of.Ge.Ne h h_d
    rw [@Tensor.Permute.eq.Ite]
    simp
    split_ifs with h_d0 h_i? h_i h_length
    ·
      omega
    ·
      have h_s : 0 < s.length := by omega
      have h_i : i = ⟨0, h_s⟩ := by aesop
      subst h_i
      simp_all
      apply SEqCast.of.SEq.Eq
      ·
        simp [Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
      ·
        rw [@Tensor.Permute.eq.Ite]
        simp
        split_ifs with h_s
        ·
          subst h_s
          apply SEq_Cast.of.SEq.Eq
          ·
            simp
            rw [EqPermute__0]
          ·
            simp at h_s
        ·
          apply SEq_Cast.of.SEq.Eq
          ·
            simp [List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0]
          ·
            sorry
    ·
      apply SEq.of.SEqDataS.Eq
      ·
        rw [EqPermuteS.of.Add.ge.SubLength_1 (s := s) (i := i) (d := d) (by omega)]
        rw [EqPermuteS.of.Add.ge.SubLength_1 (s := s) (i := i) (d := s.length - i) (by omega)]
      ·
        simp
        sorry
    ·
      omega
    ·
      omega


-- created on 2025-10-29
