import sympy.Basic
import Mathlib.MeasureTheory.Group.Measure

open MeasureTheory


@[path]
private lemma main
  {μ : Measure ℝ} [Measure.IsAddLeftInvariant μ]
  {h : ℝ}
  {f : α → ℝ}
  {S : Set α} :
-- imply
  μ (⋃ x ∈ S, {h + f x}) = μ (⋃ x ∈ S, {f x}) := by
-- proof
  have h_eq : ⋃ x ∈ S, {h + f x} = (fun y => -h + y) ⁻¹' (⋃ x ∈ S, {f x}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    ·
      rintro ⟨x, hxS, rfl⟩
      refine ⟨x, hxS, by ring⟩
    ·
      rintro ⟨x, hxS, hx⟩
      refine ⟨x, hxS, by linarith⟩
  rw [h_eq]
  apply measure_preimage_add


-- created on 2026-10-08
