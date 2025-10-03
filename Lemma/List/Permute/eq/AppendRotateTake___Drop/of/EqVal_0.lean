import Lemma.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
import Lemma.Algebra.Gt_0
import Lemma.Algebra.Eq_Mk
open Algebra List


@[main]
private lemma main
  {a : List α}
  {d : Fin a.length}
-- given
  (h_d : d.val = 0)
  (i : ℕ) :
-- imply
  a.permute d i = (a.take (i + 1)).rotate 1 ++ a.drop (i + 1) := by
-- proof
  have h_length := Gt_0 d
  have := Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0 h_length i
  rw [← this]
  have h_mk := Eq_Mk d
  simp [h_d] at h_mk
  rw [h_mk]


-- created on 2025-07-14
