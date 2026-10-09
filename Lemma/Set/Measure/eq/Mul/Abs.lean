import Mathlib
import sympy.Basic

open scoped Pointwise


@[path]
private lemma main
  {f : ℝ → ℝ}
  {h : ℝ}
  {S : Set ℝ} :
-- imply
  MeasureTheory.volume ((fun x => f x * h) '' S)
    = ENNReal.ofReal |h| * MeasureTheory.volume (f '' S) := by
-- proof
  have himg : (fun x => f x * h) '' S = h • (f '' S) := by
    ext y
    constructor
    ·
      rintro ⟨x, hx, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, mul_comm _ _⟩
    ·
      rintro ⟨z, hz, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, hx, mul_comm _ _⟩
  rw [himg]
  simp only [MeasureTheory.Measure.addHaar_smul, Module.finrank_self, pow_one]


-- created on 2026-10-07
