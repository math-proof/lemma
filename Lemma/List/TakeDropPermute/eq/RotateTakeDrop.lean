import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.EqTake.of.LeLength
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.EqPermuteS.of.Add.ge.SubLength_1
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ):
-- imply
  ((s.permute i d).drop i).take (d + 1) = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  have h_permute := DropPermute.eq.AppendRotateTakeDrop i d
  if h : s.length > i + d then
    have h_permute := congrArg (·.take (d + 1)) h_permute
    simp at h_permute
    rwa [EqTakeAppend.of.Eq_Length] at h_permute
    simp
    omega
  else
    have h_permute := congrArg (·.take (s.length - i)) h_permute
    simp at h_permute
    rw [EqTakeAppend.of.Eq_Length] at h_permute
    ·
      rw [EqPermuteS.of.Add.ge.SubLength_1 (by omega)] at h_permute ⊢
      rwa [EqTake.of.LeLength] at h_permute ⊢
      .
        simp
        omega
      .
        simp
    ·
      simp
      omega


-- created on 2025-10-23
-- updated on 2025-10-27
