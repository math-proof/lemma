import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic
import sympy.core.singleton


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfiniteNeg ↔ x.Infinite ∧ x < 0 := by
-- proof
  simp [Hyperreal.InfiniteNeg, Hyperreal.Infinite, Hyperreal.InfinitePos]
  constructor <;> 
    intro h
  ·
    constructor
    ·
      right
      assumption
    ·
      apply h
  ·
    obtain ⟨h | h, h_x⟩ := h
    ·
      have h := h 0
      simp at h
      linarith
    ·
      assumption


-- created on 2025-12-25
