import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Nat.ValSub.eq.SubValS.of.Gt
import Lemma.Nat.Sub.ge.One.of.Lt
import Lemma.Algebra.LtValS.of.Lt
import Lemma.Nat.EqSub_Sub.of.Gt
import Lemma.Nat.Sub.ge.One.of.Gt
import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.LtSub.of.Lt
import Lemma.Algebra.Eq_0.of.Eq_Sub_1
import Lemma.Nat.Ge_Sub_1
import Lemma.Algebra.EqAdd_Sub.of.Gt
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.Nat.GeSub_1.of.Gt
import Lemma.Nat.Le.of.LtSub_1
import Lemma.Nat.LeSub.is.Le_Add
import Lemma.Nat.Eq.of.Le.Le
import Lemma.Algebra.Gt.of.Ge.Gt
import Lemma.Algebra.Le.of.LeSubS.Le
import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Algebra.Gt.of.Gt.Ge
import Lemma.Algebra.Le.of.Le_Sub
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Nat.Ge_1.of.Gt
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.Eq.of.EqSubS.Ge.Ge
open Bool List Algebra Nat
set_option maxHeartbeats 300000


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_ij : i < j) :
-- imply
  let d := j - i
  s.swap i j = (s.permute ⟨i, by linarith⟩ (d - 1)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) := by
-- proof
  intro d
  suffices h : s.swap i j = (s.permute ⟨i, by linarith⟩ (d - 1 : ℕ)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) by
    rwa [CoeSub.eq.SubCoeS.of.Ge] at h
    simp [d]
    apply Sub.ge.One.of.Lt h_ij
  have h_id : i + (d - 1) < s.length := by omega
  ext k x
  by_cases h_k_length : k < s.length
  ·
    have h_k : k < (s.swap i j).length := by
      simpa [LengthSwap.eq.Length]
    simp [h_k]
    have h_k : k < ((s.permute ⟨i, by linarith⟩ (d - 1 : ℕ)).permute ⟨j, by simpa [LengthPermute.eq.Length]⟩ (-d)).length := by
      simpa [LengthPermute.eq.Length]
    simp [h_k]
    apply IffEqS.of.Eq
    rw [GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt h_ij h_j h_k_length]
    split_ifs with h_ki h_kj
    ·
      simp [h_ki]
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length]
      .
        apply Eq.symm
        split_ifs with h_lt h_1 h_eq
        ·
          simp [d] at h_lt
          omega
        ·
          simp only [GetElem.getElem]
          simp
          rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id]
          split_ifs with h_lt' h_1 h_eq'
          ·
            rfl
          ·
            simp [d] at h_1
            omega
          ·
            simp at h_eq'
            omega
          ·
            rfl
        .
          simp [d] at h_lt h_1
          omega
        .
          simp at h_eq
          omega
      .
        simp [LengthPermute.eq.Length]
        linarith
    ·
      simp [h_kj]
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      ·
        simp [d] at h_lt
        omega
      ·
        simp [d] at h_1
        omega
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id]
        .
          split_ifs with h_lt' h_1 h_eq'
          ·
            simp at h_lt'
            omega
          ·
            simp [d] at h_1
            omega
          ·
            rfl
          ·
            simp [d] at h_eq'
            omega
        .
          apply LtSub.of.Lt h_j
      ·
        linarith
    ·
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id h_k_length]
        split_ifs with h_lt' h_1 h_eq'
        rfl
        repeat simp at h_lt h_lt'; omega
      ·
        simp at h_lt h_1
        simp [h_1]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id h_j]
        split_ifs with h_lt' h_1' h_eq'
        repeat omega
      ·
        simp at h_lt h_1 h_eq
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id]
        ·
          split_ifs with h_lt' h_1 h_eq'
          ·
            simp at h_lt'
            omega
          ·
            simp [EqAddSub.of.Ge (by omega : k ≥ 1)]
          ·
            simp [d] at h_eq'
            omega
          ·
            simp at h_1
            omega
        ·
          apply LtSub.of.Lt h_k_length
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length h_id h_k_length]
        split_ifs with h_lt' h_1 h_eq'
        ·
          rfl
        ·
          simp at h_eq h_1
          omega
        ·
          simp at h_eq h_eq'
          omega
        ·
          rfl
  ·
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    ·
      simpa [LengthPermute.eq.Length]
    ·
      rwa [LengthSwap.eq.Length]


-- created on 2025-06-21
