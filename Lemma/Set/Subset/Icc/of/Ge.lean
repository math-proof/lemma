import Lemma.Set.Subset.Icc.of.Le
import sympy.sets.sets
import sympy.Basic
open Set


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h : x ≥ y) :
-- imply
  Set.Icc x y ⊆ Set.Icc y x :=
-- proof
  Subset.Icc.of.Le h


-- created on 2021-04-10
