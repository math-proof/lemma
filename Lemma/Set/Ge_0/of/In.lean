import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Set.Ici 0) :
-- imply
  0 ≤ x := by
-- proof
  exact h


-- created on 2021-09-03
