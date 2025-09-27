import Lemma.Algebra.LengthPermute.eq.Length
import Lemma.Algebra.LengthSwap.eq.Length
import Lemma.Logic.IffEqS.of.Eq
import Lemma.Algebra.GetElem!.eq.None.of.Ge_Length
import Lemma.Algebra.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length
import Lemma.Algebra.EqSwap.of.Ge_Length
import Lemma.Algebra.Permute.eq.Permute__Sub.of.Add.ge.SubLength_1
import Lemma.Algebra.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Algebra.Le.of.Lt_Add_1
open Algebra Logic


@[main]
private lemma main
  {a : List α}
-- given
  (i : Fin a.length)
  (d : ℕ) :
-- imply
  a.permute i (d + 1) = (a.permute i d).swap (i + d) (i + d + 1) := by
-- proof
  have h_length := LengthPermute.eq.Length a i (d + 1)
  have h_length' := LengthSwap.eq.Length (a.permute i d) (i + d) (i + d + 1)
  rw [LengthPermute.eq.Length] at h_length'
  by_cases h : i + d + 1 ≥ a.length
  ·
    let h' := h
    have := LengthPermute.eq.Length a i d
    simp [← this] at h
    rw [EqSwap.of.Ge_Length h]
    rw [Permute.eq.Permute__Sub.of.Add.ge.SubLength_1]
    rw [Permute.eq.Permute__Sub.of.Add.ge.SubLength_1 (d := d)]
    ·
      simp
      norm_cast
    ·
      simp
      norm_cast
      linarith
  ·
    simp at h
    ext j t
    by_cases h_j : j < a.length
    ·
      let h_j' := h_j
      rw [← h_length] at h_j
      simp [h_j]
      rw [← h_length'] at h_j'
      simp [h_j']
      apply IffEqS.of.Eq
      rw [GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt_Length (by rw [LengthPermute.eq.Length]; linarith) (by rw [LengthPermute.eq.Length]; linarith) (by rw [LengthPermute.eq.Length]; linarith)]
      split_ifs with h₀ h₁
      ·
        simp [h₀]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        simp [(show a.permute i (↑d + 1) = a.permute i ↑(d + 1) by simp)]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        split_ifs with h_lt h_lt' h_eq
        ·
          linarith
        ·
          rfl
        ·
          linarith
        ·
          linarith
      ·
        simp [h₁]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        simp [(show a.permute i (↑d + 1) = a.permute i ↑(d + 1) by simp)]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        split_ifs with h_lt h_lt' h_eq
        ·
          linarith
        ·
          linarith
        ·
          rfl
        ·
          contradiction
      ·
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        simp [(show a.permute i (↑d + 1) = a.permute i ↑(d + 1) by simp)]
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by linarith) (by linarith)]
        split_ifs with h_lt h_lt? h_j h_eq? h_lt' h_j'
        ·
          rfl
        ·
          rfl
        ·
          simp at h_j
          have h_le := Le.of.Lt_Add_1 h_lt?
          have h_eq := Eq.of.Ge.Le h_j h_le
          contradiction
        ·
          contradiction
        ·
          contradiction
        ·
          linarith
        ·
          rfl
    ·
      simp at h_j
      let h_j' := h_j
      rw [← h_length] at h_j
      rw [GetElem!.eq.None.of.Ge_Length h_j]
      rw [← h_length'] at h_j'
      simp_all [GetElem!.eq.None.of.Ge_Length h_j']


-- created on 2025-06-07
-- updated on 2025-06-08
