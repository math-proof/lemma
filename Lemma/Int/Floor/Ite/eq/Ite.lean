import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {g h : ℝ → ℝ} :
-- imply
  ⌊if x > 0 then g x else h x⌋ = if x > 0 then ⌊g x⌋ else ⌊h x⌋ := by
-- proof
  split_ifs <;> rfl


-- created on 2019-05-14
