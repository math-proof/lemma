/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part7


namespace MetaMathlibExt

theorem ff3_edgeDominoes_matching_iff {n : ℕ} (E : Finset (ff3Edge n)) :
    ff3IsMatching (ff3EdgeDominoes E) ↔ ff3IsEdgeMatching E := by
  constructor
  · intro hD e he f hf hne
    apply hD.2 (ff3EdgeDomino e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      (ff3EdgeDomino f) (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    exact fun h ↦ hne (ff3_edgeDomino_injective h)
  · intro hE
    refine ⟨?_, ?_⟩
    · intro d hd
      obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hd
      exact ff3_edgeDomino_isDomino e
    · intro d hd e he hde
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
      exact hE a ha b hb fun hab ↦ hde (congrArg ff3EdgeDomino hab)

theorem ff3_fault_domino_eq_horizontal {n : ℕ}
    {d : Finset (TilingCell (n + 1))} (hd : ff3IsDomino d) {x y : TilingCell (n + 1)}
    (hx : x ∈ d) (hy : y ∈ d) (k : Fin n) (hrow : x.1 = y.1)
    (hxcol : x.2.val = k.val) (hycol : y.2.val = k.val + 1) :
    d = ff3HorizontalDomino x.1 k := by
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  have hsub : ({x, y} : Finset (TilingCell (n + 1))) ⊆ d := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hpair : ({x, y} : Finset (TilingCell (n + 1))) = d := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hd.1]
    simp [hxy]
  have hx' : x = (x.1, k.castSucc) := by
    apply Prod.ext
    · rfl
    · exact Fin.ext hxcol
  have hy' : y = (x.1, k.succ) := by
    apply Prod.ext
    · exact hrow.symm
    · exact Fin.ext hycol
  rw [← hpair, hx', hy']
  rfl

theorem ff3_edgeDominoes_faultFree_iff {n : ℕ} (E : Finset (ff3Edge n)) :
    IsVerticalFaultFree (ff3EdgeDominoes E) ↔ ff3CrossesEveryCut E := by
  constructor
  · intro h k
    obtain ⟨d, hd, x, hx, y, hy, hrow, hxcol, hycol⟩ := h k.val (by omega)
    obtain ⟨e, he, hdomino⟩ := Finset.mem_image.mp hd
    let k' : Fin n := ⟨k.val, k.isLt⟩
    have hdEq : d = ff3HorizontalDomino x.1 k' :=
      ff3_fault_domino_eq_horizontal (hdomino ▸ ff3_edgeDomino_isDomino e)
        hx hy k' hrow hxcol hycol
    have heEq : e = Sum.inl (x.1, k') := by
      apply ff3_edgeDomino_injective
      change ff3EdgeDomino e = ff3HorizontalDomino x.1 k'
      rw [hdomino, hdEq]
    refine ⟨x.1, ?_⟩
    simpa [k'] using heEq ▸ he
  · intro h k hk
    let k' : Fin n := ⟨k, by omega⟩
    obtain ⟨r, hr⟩ := h k'
    refine ⟨ff3HorizontalDomino r k', Finset.mem_image.mpr ⟨Sum.inl (r, k'), hr, rfl⟩,
      (r, k'.castSucc), by simp [ff3HorizontalDomino],
      (r, k'.succ), by simp [ff3HorizontalDomino], ?_⟩
    simp [k']

end MetaMathlibExt
