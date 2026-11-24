module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

theorem ff3_edgeDominoes_edgesOf {n : ℕ}
    {D : Finset (Finset (TilingCell (n + 1)))} (hD : ∀ d ∈ D, ff3IsDomino d) :
    ff3EdgeDominoes (ff3EdgesOf D) = D := by
  ext d
  constructor
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp he).2
  · intro hd
    rcases (ff3_isDomino_iff d).mp (hD d hd) with h | h
    · obtain ⟨r, k, rfl⟩ := h
      apply Finset.mem_image.mpr
      refine ⟨Sum.inl (r, k), ?_, rfl⟩
      simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hd
    · obtain ⟨r, k, rfl⟩ := h
      apply Finset.mem_image.mpr
      refine ⟨Sum.inr (r, k), ?_, rfl⟩
      simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hd

theorem ff3_edgesOf_edgeDominoes {n : ℕ} (E : Finset (ff3Edge n)) :
    ff3EdgesOf (ff3EdgeDominoes E) = E := by
  ext e
  simp only [ff3EdgesOf, Finset.mem_filter, Finset.mem_univ, true_and,
    ff3EdgeDominoes, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfe⟩
    exact (ff3_edgeDomino_injective hfe).symm ▸ hf
  · intro he
    exact ⟨e, he, rfl⟩

end MetaMathlibExt
