import Def.Data.List.List.Basic
import Lemma.List.All_EqUFnS.of.All_Eq
import Instance.Data.List.List
open List


@[path]
private lemma main
  {s : List α}
-- given
  (h : IsConstant.is_constant s)
  (f : α → β) :
-- imply
  IsConstant.is_constant (s.map f) := by
-- proof
  induction s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons =>
    simp [IsConstant.is_constant]
    exact All_EqUFnS.of.All_Eq h


-- created on 2024-07-01
-- updated on 2026-10-26
