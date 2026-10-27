import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {y : ℝ}
-- given
  (h : y ∈ Set.Ioc 0 1) :
-- imply
  Real.log y ≤ 0 :=
-- proof
  Real.log_nonpos h.1.le h.2


-- created on 2023-04-17
-- updated on 2026-10-26
