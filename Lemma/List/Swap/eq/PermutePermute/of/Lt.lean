import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Algebra.ValSub.eq.SubValS.of.Gt
import Lemma.Algebra.Sub.ge.One.of.Lt
import Lemma.Algebra.LtValS.of.Lt
import Lemma.Algebra.EqSub_Sub.of.Gt
import Lemma.Algebra.Sub.ge.One.of.Gt
import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Algebra.LtSub.of.Lt
import Lemma.Algebra.Eq_0.of.Eq_Sub_1
import Lemma.Algebra.Ge_Sub_1
import Lemma.Algebra.EqAdd_Sub.of.Gt
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.Algebra.GeSub_1.of.Gt
import Lemma.Algebra.Le.of.LtSub_1
import Lemma.Algebra.LeSub.is.Le_Add
import Lemma.Nat.Eq.of.Le.Le
import Lemma.Algebra.Gt.of.Ge.Gt
import Lemma.Algebra.Le.of.LeSubS.Le
import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Algebra.Gt.of.Gt.Ge
import Lemma.Algebra.Le.of.Le_Sub
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.Ge_1.of.Gt
import Lemma.Algebra.EqAddSub.of.Ge
import Lemma.Algebra.Eq.of.EqSubS.Ge.Ge
open Algebra List Bool Nat
set_option maxHeartbeats 300000


@[main]
private lemma main
  {s : List α}
  {i j : Fin s.length}
-- given
  (h : i < j) :
-- imply
  let d := j - i
  s.swap i j = (s.permute i (d - 1)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) := by
-- proof
  have h_ij := LtValS.of.Lt h
  have h_Ge_1 := Sub.ge.One.of.Gt h_ij
  intro d
  suffices h : s.swap i j = (s.permute i (d - 1 : ℕ)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) by
    rw [CoeSub.eq.SubCoeS.of.Ge] at h
    ·
      assumption
    ·
      simp [d]
      rw [ValSub.eq.SubValS.of.Gt (by assumption)]
      apply Sub.ge.One.of.Lt
      apply LtValS.of.Lt
      assumption
  have h_d : d.val ≥ 1 := by
    simp_all [d]
    rwa [ValSub.eq.SubValS.of.Gt (by assumption)]
  have h_dj : d.val ≤ j.val := by
    simp_all [d]
    apply Le.of.Lt
    assumption
  have h_Gt_0 : j.val > 0 := by
    linarith
  have h_j : j.val = i.val + d.val := by
    simp [d]
    rw [ValSub.eq.SubValS.of.Gt (by assumption)]
    rw [EqAdd_Sub.of.Gt (by assumption)]
  have h_i : i.val = j.val - d.val := by
    rw [h_j]
    simp_all
  have h_j' : j.val < s.length := by
    simp
  have h_Sub_1 : j.val - 1 ≥ i.val := by
    apply GeSub_1.of.Gt
    assumption
  have h_ij' : i + (d - 1) = j.val - 1 := by
    rw [Add_Sub.eq.SubAdd.of.Ge (by assumption)]
    rw [← h_j]
  have h_length : i + (d - 1) < s.length := by
    rw [h_ij']
    apply LtSub.of.Lt
    assumption
  have h_ge := Ge_Sub_1 j.val
  ext k x
  by_cases h_k : k < s.length
  ·
    have h_k : k < (s.swap i j).length := by
      simpa [LengthSwap.eq.Length]
    simp [h_k]
    have h_k : k < ((s.permute i (d - 1 : ℕ)).permute ⟨j, by simp [LengthPermute.eq.Length]⟩ (-d)).length := by
      simpa [LengthPermute.eq.Length]
    simp [h_k]
    apply IffEqS.of.Eq
    rw [GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt (by assumption) (by assumption) (by assumption)]
    split_ifs with h_ki h_kj
    ·
      simp [h_ki]
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simp [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt
      ·
        simp [d] at h_lt
        rw [ValSub.eq.SubValS.of.Gt (by assumption)] at h_lt
        rw [EqSub_Sub.of.Gt (by assumption)] at h_lt
        linarith
      ·
        simp only [GetElem.getElem]
        simp
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        ·
          split_ifs with h_lt' h_1 h_eq'
          ·
            rfl
          ·
            rw [h_ij'] at h_1
            linarith
          ·
            simp at h_lt h_1
            simp at h_eq'
            rw [h_ij'] at h_eq'
            have := Eq_0.of.Eq_Sub_1 h_eq'
            linarith
          ·
            rfl
        ·
          assumption
    ·
      simp [h_kj]
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simp [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      ·
        linarith
      ·
        linarith
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        ·
          split_ifs with h_lt' h_1 h_eq'
          ·
            linarith
          ·
            rw [h_ij'] at h_1
            linarith
          ·
            rfl
          ·
            rw [h_ij'] at h_eq'
            contradiction
        ·
          assumption
        ·
          apply LtSub.of.Lt
          assumption
      ·
        linarith
    ·
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by assumption) (by assumption)]
        split_ifs with h_lt' h_1 h_eq'
        ·
          rfl
        ·
          simp at h_lt
          rw [← h_i] at h_lt
          linarith
        ·
          simp at h_lt
          rw [← h_i] at h_lt
          linarith
        ·
          rfl
      ·
        simp at h_lt h_1
        simp [h_1]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by assumption) (by assumption)]
        split_ifs with h_lt' h_1' h_eq'
        ·
          linarith
        ·
          rw [h_ij'] at h_1'
          have := Gt.of.Ge.Gt h_ge h_1'
          simp at this
        ·
          rw [h_ij'] at h_eq'
          simp_all [Eq_0.of.Eq_Sub_1 h_eq']
        ·
          rw [← h_i] at h_1
          contradiction
      ·
        simp at h_lt h_1 h_eq
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by assumption)]
        ·
          split_ifs with h_lt' h_1 h_eq'
          ·
            have h_lt' := Le.of.LtSub_1 h_lt'
            have h_lt := LeSub.of.Le_Add.nat h_lt
            rw [← h_i] at h_lt
            have h_eq := Eq.of.Le.Le h_lt h_lt'
            contradiction
          ·
            have h_le := LeSub.of.Le_Add.nat h_lt
            rw [← h_i] at h_le
            have h_gt := Gt.of.Ge.Ne h_le h_ki
            have h_ge := Ge_1.of.Gt h_gt
            simp [EqAddSub.of.Ge h_ge]
          ·
            rw [h_ij'] at h_eq'
            have h_lt := LeSub.of.Le_Add.nat h_lt
            rw [← h_i] at h_lt
            have h_gt := Gt.of.Ge.Ne h_lt h_ki
            have h_ge := Ge_1.of.Gt h_gt
            have h_eq' := Eq.of.EqSubS.Ge.Ge h_ge (by assumption) h_eq'
            contradiction
          ·
            simp at h_1
            rw [h_ij'] at h_1
            simp at h_lt'
            have h_lt' := Le.of.Le_Sub h_lt'
            have h_gt := Gt.of.Ge.Ne h_lt' h_ki
            have h_ge := Ge_1.of.Gt h_gt
            have := Le.of.LeSubS.Le h_ge h_1
            have h_eq := Eq.of.Le.Le this h_eq
            contradiction
        ·
          apply LtSub.of.Lt (by assumption)
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by assumption) (by assumption)]
        split_ifs with h_lt' h_1 h_eq'
        ·
          rfl
        ·
          simp at h_eq
          rw [h_ij'] at h_1
          have := Lt.of.Lt.Lt h_eq h_1
          have := Gt.of.Gt.Ge this h_ge
          simp at this
        ·
          simp at h_eq
          rw [h_ij'] at h_eq'
          rw [h_eq'] at h_eq
          have := Gt.of.Ge.Gt h_ge h_eq
          simp at this
        ·
          rfl
  ·
    simp at h_k
    repeat rw [GetElem.eq.None.of.Ge_Length]
    ·
      simpa [LengthPermute.eq.Length]
    ·
      rwa [LengthSwap.eq.Length]


-- created on 2025-06-21
