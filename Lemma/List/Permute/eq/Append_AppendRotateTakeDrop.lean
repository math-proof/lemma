import Lemma.Algebra.LtVal
import Lemma.Algebra.Sub.gt.Zero.is.Lt
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.List.SliceDrop.eq.Slice_AddS
open Algebra List


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  s.permute i d = s.take i ++ (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)) := by
-- proof
  have h_i := LtVal i
  have h_i := Sub.gt.Zero.of.Lt.nat h_i
  have h_length := LengthDrop.eq.SubLength s i
  rw [← h_length] at h_i
  have := Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 h_i d
  rw [← this]
  unfold List.permute
  simp
  rw [SliceDrop.eq.Slice_AddS]


-- created on 2025-06-17
