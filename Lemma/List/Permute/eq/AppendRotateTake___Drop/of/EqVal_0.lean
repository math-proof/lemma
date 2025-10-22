import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Nat.Gt_0
import Lemma.Algebra.Eq_Mk
open Algebra List Nat


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i.val = 0)
  (d : ℕ) :
-- imply
  s.permute i d = (s.take (d + 1)).rotate 1 ++ s.drop (d + 1) := by
-- proof
  rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
  have h_mk := Eq_Mk i
  simp [h] at h_mk
  rw [h_mk]


-- created on 2025-07-14
