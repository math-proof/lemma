import sympy.sets.sets
import sympy.Basic
open Finset


@[main]
private lemma main
  {e a b : ℤ}
-- given
  (h : e ∉ Finset.Ico a b) :
-- imply
  e < a ∨ e ≥ b := by
-- proof
  simp only [Finset.mem_Ico] at h
  omega


-- created on 2026-10-03
