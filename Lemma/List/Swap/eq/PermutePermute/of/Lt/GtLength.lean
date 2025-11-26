import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetSwap.eq.Ite.of.GtLength.GtLength.Lt
import Lemma.List.GetPermute__Neg.eq.Ite.of.GtLength
import Lemma.List.GetPermute.eq.Ite.of.GtLength.GtLength
import Lemma.Nat.CoeSub.eq.SubCoeS.of.Ge
import Lemma.List.GetElem.eq.None.of.Ge_Length
open Bool List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_ij : i < j) :
-- imply
  let d := j - i
  s.swap i j = (s.permute ⟨i, by linarith⟩ (d - 1)).permute ⟨j, by simpa⟩ (-d) := by
-- proof
  intro d
  suffices h : s.swap i j = (s.permute ⟨i, by linarith⟩ (d - 1 : ℕ)).permute ⟨j, by simpa⟩ (-d) by
    rwa [CoeSub.eq.SubCoeS.of.Ge] at h
    grind
  have h_id : i + (d - 1) < s.length := by omega
  ext k x
  if h_k_length : k < s.length then
    have h_k : k < (s.swap i j).length := by
      simpa [LengthSwap.eq.Length]
    apply IffEqS.of.Eq
    simp [h_k]
    rw [GetSwap.eq.Ite.of.GtLength.GtLength.Lt h_ij h_j h_k_length]
    split_ifs with h_ki h_kj
    ·
      simp_all
      rw [GetPermute__Neg.eq.Ite.of.GtLength]
      ·
        apply Eq.symm
        split_ifs with h_lt h_1 h_eq
        grind
        simp
        rw [GetPermute.eq.Ite.of.GtLength.GtLength]
        repeat grind
      ·
        simp
        linarith
    ·
      simp_all
      rw [GetPermute__Neg.eq.Ite.of.GtLength (by simpa)]
      apply Eq.symm
      split_ifs with h_lt h_1 h_eq
      repeat grind
      rw [GetPermute.eq.Ite.of.GtLength.GtLength]
      repeat grind
    ·
      simp_all
      rw [GetPermute__Neg.eq.Ite.of.GtLength (by simpa)]
      apply Eq.symm
      split_ifs <;>
      ·
        try simp
        rw [GetPermute.eq.Ite.of.GtLength.GtLength]
        repeat grind
  else
    simp at h_k_length
    repeat rw [GetElem.eq.None.of.Ge_Length]
    ·
      simpa
    ·
      rwa [LengthSwap.eq.Length]


-- created on 2025-06-21
-- updated on 2025-10-26
