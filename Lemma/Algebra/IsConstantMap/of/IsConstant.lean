import sympy.vector.vector
import Lemma.Logic.All_EqUFnS.of.All_Eq
open Logic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s is constant)
  (f : α → β) :
-- imply
  (s.map f) is constant := by
-- proof
  induction s with
  | nil =>
    simp [IsConstant.is_constant]
  | cons =>
    simp [IsConstant.is_constant]
    exact All_EqUFnS.of.All_Eq.list h


@[main]
private lemma vector
  {s : List.Vector α n}
-- given
  (h: s is constant)
  (f : α → β) :
-- imply
  (s.map f) is constant :=
-- proof
  main h f


-- created on 2024-07-01
-- updated on 2025-02-23
