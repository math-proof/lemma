import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Icc y x ⊆ Set.Icc x y := by
-- proof
  exact fun t ht => ⟨h.trans ht.1, ht.2.trans h⟩


@[path]
private lemma lower
  {x y z : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Ioc z x ⊆ Set.Ioc z y := by
-- proof
  exact Set.Ioc_subset_Ioc_right h


@[path]
private lemma upper
  {x y z : ℝ}
-- given
  (h : x ≤ y) :
-- imply
  Set.Ioc y z ⊆ Set.Ioc x z := by
-- proof
  exact Set.Ioc_subset_Ioc_left h


-- created on 2020-06-03
