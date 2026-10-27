import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x > 0) :
-- imply
  x ∈ Set.Ioi 0 := by
-- proof
  exact Set.mem_Ioi.mpr h


-- created on 2020-04-24
