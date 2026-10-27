import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {y : ℝ}
-- given
  (h : y ∈ Set.Ici 1) :
-- imply
  0 ≤ Real.log y := by
-- proof
  exact Real.log_nonneg h


-- created on 2023-04-17
-- updated on 2026-10-26
