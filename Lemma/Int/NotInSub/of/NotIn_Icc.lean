import Mathlib.Order.Interval.Set.Basic
import sympy.Basic


@[main]
private lemma main
  {e a b t : ℝ}
  -- given
  (h : e ∉ Set.Icc a b)
  -- imply
  : e - t ∉ Set.Icc (a - t) (b - t) := by
  -- proof
  by_contra h2
  rw [Set.mem_Icc] at h2
  rw [Set.mem_Icc] at h
  exact h ⟨by linarith, by linarith⟩

-- created on 2018-07-11
