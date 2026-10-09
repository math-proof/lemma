import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ} :
-- imply
  max ⌈x⌉ ⌈y⌉ = ⌈max x y⌉ := by
-- proof
  exact Int.ceil_mono.map_max.symm


-- created on 2020-01-24
