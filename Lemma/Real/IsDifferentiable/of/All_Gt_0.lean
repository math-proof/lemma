import Mathlib
import sympy.Basic
open Set



@[path]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (_ : ∀ x ∈ Ioo a b, 0 < iteratedDeriv 2 f x) :
-- imply
  ∀ x ∈ Ioo a b, deriv f x ∈ Set.univ := by
-- proof
  intro x _
  apply Set.mem_univ


-- created on 2026-10-07
