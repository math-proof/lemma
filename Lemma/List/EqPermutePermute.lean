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
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.Eq.of.EqSubS.Ge.Ge
open Bool List Algebra Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_ij : i < j) :
-- imply
  let d := j - i
  (s.permute ⟨i, by linarith⟩ d).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) = s := by
-- proof
  intro d
  ext k x
  by_cases h_k_length : k < s.length
  .
    simp [h_k_length]
    have h_k : k < ((s.permute ⟨i, by linarith⟩ d).permute ⟨j, by simpa [LengthPermute.eq.Length]⟩ (-d)).length := by
      simpa [LengthPermute.eq.Length]
    simp [h_k]
    apply IffEqS.of.Eq
    rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
    split_ifs with h_lt h_1 h_eq
    .
      simp [d] at h_lt
      simp [EqSub_Sub.of.Gt h_ij] at h_lt
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length _ h_k_length]
      .
        simp [h_lt]
      .
        simp [d]
        simpa [EqAdd_Sub.of.Gt h_ij]
    .
      simp [d] at h_1
      simp [EqSub_Sub.of.Gt h_ij] at h_1
      subst h_1
      simp
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length _ h_j]
      .
        split_ifs with h_lt' h_1 h_eq'
        .
          linarith
        .
          simp [d] at h_1
          omega
        .
          rfl
        .
          simp [d] at h_eq'
          omega
      .
        simp [d]
        simpa [EqAdd_Sub.of.Gt h_ij]
    .
      simp [d] at h_lt h_1 h_eq
      simp [EqSub_Sub.of.Gt h_ij] at h_1
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
      .
        split_ifs with h_lt' h_1 h_eq'
        .
          simp at h_lt'
          omega
        .
          simp [EqAddSub.of.Ge (by omega : k ≥ 1)]
        .
          simp [d] at h_eq'
          omega
        .
          simp [d] at h_1
          omega
      .
        simp [d]
        simpa [EqAdd_Sub.of.Gt h_ij]
      .
        omega
    .
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
      .
        split_ifs with h_lt' h_1 h_eq'
        .
          rfl
        .
          simp at h_eq h_1
          omega
        .
          simp at *
          omega
        .
          simp [d] at *
      .
        simp [d]
        omega
  .
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    repeat simpa [LengthPermute.eq.Length]


-- created on 2025-10-12
