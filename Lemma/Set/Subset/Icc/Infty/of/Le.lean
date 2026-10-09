import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Ici y ⊆ Set.Ici x := by
-- proof
  exact Set.Ici_subset_Ici.mpr h


-- created on 2021-02-26
