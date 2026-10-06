import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Iic x ⊆ Set.Iic y := by
-- proof
  exact Set.Iic_subset_Iic.mpr h


-- created on 2020-11-23
