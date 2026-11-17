import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.EqTake.of.LeLength
import Lemma.List.EqTakeAppend.of.Eq_Length
import Lemma.List.Permute.of.Add.ge.SubLength_1
import Theorem.Data.List.List.Part2
open List


@[path, comm]
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
    rw [EqTakeAppend.of.Eq_Length] at h_permute
    · assumption
    · simp
      omega
  else
    have h_permute := congrArg (·.take (s.length - i)) h_permute
    rw [EqTakeAppend.of.Eq_Length] at h_permute
    ·
      rw [Permute.of.Add.ge.SubLength_1 (by omega)] at h_permute ⊢
      have hlen_s : ((s.permute i ↑(s.length - 1 - ↑i)).drop i).length ≤ s.length - i := by
        rw [List.length_drop, List.length_permute]
      have hlen_d : ((s.permute i ↑(s.length - 1 - ↑i)).drop i).length ≤ d + 1 := by
        rw [List.length_drop, List.length_permute]
        omega
      rw [EqTake.of.LeLength hlen_s] at h_permute
      rw [EqTake.of.LeLength hlen_d]
      exact h_permute
    ·
      simp
      omega


-- created on 2025-10-23
-- updated on 2025-10-27
