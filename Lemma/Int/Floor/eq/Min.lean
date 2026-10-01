import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  ⌊min x y⌋ = min ⌊x⌋ ⌊y⌋ := by
-- proof
  exact Int.floor_mono.map_min


-- created on 2026-09-27
