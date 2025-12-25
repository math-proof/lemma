import Mathlib.Analysis.Real.Hyperreal
import sympy.Basic
import sympy.core.singleton


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ x.Infinite ∧ x > 0 := by
-- proof
  simp [Hyperreal.InfinitePos, Hyperreal.Infinite, Hyperreal.InfiniteNeg]
  constructor <;> 
    intro h
  ·
    constructor
    ·
      left
      assumption
    ·
      apply h
  ·
    obtain ⟨h | h, h_x⟩ := h
    ·
      assumption
    ·
      have h := h 0
      simp at h
      linarith


-- created on 2025-12-25
