module

public import Theorem.List.Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0
public import Theorem.Nat.Gt_0
public import Theorem.Fin.Eq_Fin

public section

open List Nat Fin


public theorem List.Permute.eq.AppendRotateTake___Drop.of.EqVal_0
  {s : List α}
  {i : Fin s.length}
-- given
  (h : i.val = 0)
  (d : ℕ) :
-- imply
  s.permute i d = (s.take (d + 1)).rotate 1 ++ s.drop (d + 1) := by
-- proof
  rw [← Permute_0.eq.AppendRotateTake___Drop.of.GtLength_0]
  have h_mk := Eq_Fin i
  simp [h] at h_mk
  rw [h_mk]


-- created on 2025-07-14
