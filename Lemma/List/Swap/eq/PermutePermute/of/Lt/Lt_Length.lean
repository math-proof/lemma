import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.List.GetElem.eq.None.of.Ge_Length
open Bool List Nat
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
    grind
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
      ·
        apply Eq.symm
        split_ifs with h_lt h_1 h_eq
        grind
        simp
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        repeat grind
      ·
        simp [LengthPermute.eq.Length]
        linarith
    ·
      simp [h_kj]
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      repeat grind
      rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
      repeat grind
    ·
      rw [GetPermute__Neg.eq.Ite.of.Lt_Length (by simpa [LengthPermute.eq.Length])]
      apply Eq.symm
      split_ifs <;>
      ·
        try simp
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length]
        repeat grind
  ·
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    ·
      simpa [LengthPermute.eq.Length]
    ·
      rwa [LengthSwap.eq.Length]


-- created on 2025-06-21
-- updated on 2025-10-25
