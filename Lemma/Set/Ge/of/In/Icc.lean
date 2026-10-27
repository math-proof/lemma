import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n b : ℝ}
-- given
  (h : b ≤ n) :
-- imply
  n ∈ Set.Ici b := by
-- proof
  exact h


-- created on 2021-09-02
