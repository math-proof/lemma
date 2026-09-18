import sympy.Basic
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.Normed.Module.Completion


@[main]
private lemma main
  [Field K]
-- given
  (v : AbsoluteValue K ℝ):
-- imply
  IsNonarchimedean v ↔ ∀ x y z : K, v (x - z) ≤ max (v (x - y)) (v (y - z)) := by
-- proof
  constructor
  .
    intro hv x y z
    have h : (x - y) + (y - z) = x - z := by ring
    rw [← h]
    exact hv (x - y) (y - z)
  .
    intro h a b
    simpa using h (a + b) b 0


-- created on 2026-09-18
