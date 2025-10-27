import Lemma.List.EqDropAppend.of.Eq_Length
import Lemma.List.TakePermute__Neg.eq.Append_RotateDropTake
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  ((s.permute i (-d)).take (i + 1)).drop (i - d) = ((s.take (i + 1)).drop (i - d)).rotate (d ⊓ i) := by
-- proof
  have h_permute := TakePermute__Neg.eq.Append_RotateDropTake i d
  have h_permute := congrArg (·.drop (i - d)) h_permute
  simp at h_permute
  rwa [EqDropAppend.of.Eq_Length] at h_permute
  simp
  omega


-- created on 2025-10-27
