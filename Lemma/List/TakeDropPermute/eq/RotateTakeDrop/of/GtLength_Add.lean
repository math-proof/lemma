import Lemma.List.DropPermute.eq.AppendRotateTakeDrop
import Lemma.List.EqTakeAppend.of.Eq_Length
open List


@[main, comm]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h : s.length > i + d) :
-- imply
  ((s.permute i d).drop i).take (d + 1) = ((s.drop i).take (d + 1)).rotate 1 := by
-- proof
  have h_permute := DropPermute.eq.AppendRotateTakeDrop i d
  have h_permute := congrArg (·.take (d + 1)) h_permute
  simp at h_permute
  rwa [EqTakeAppend.of.Eq_Length] at h_permute
  simp
  omega


-- created on 2025-10-23
