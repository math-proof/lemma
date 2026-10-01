import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : ⌈x⌉ = 0) :
-- imply
  x ∈ Set.Ioc (-1) 0 := by
-- proof
  have := Int.ceil_eq_iff.mp h
  exact ⟨by simpa using this.1, by simpa using this.2⟩


-- created on 2019-08-12
