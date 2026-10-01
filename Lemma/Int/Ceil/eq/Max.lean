import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  ⌈max x y⌉ = max ⌈x⌉ ⌈y⌉ := by
-- proof
  exact Int.ceil_mono.map_max


-- created on 2026-09-27
