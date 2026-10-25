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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part4


namespace MetaMathlibExt

theorem ff3_horizontal_isDomino {n : ℕ} (r : Fin 3) (k : Fin n) :
    ff3IsDomino (ff3HorizontalDomino r k) := by
  refine ⟨?_, ?_⟩
  · simp [ff3HorizontalDomino, Fin.ext_iff]
  · intro x hx y hy hxy
    simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · left
      simp
    · left
      simp
    · exact (hxy rfl).elim

theorem ff3_vertical_isDomino {n : ℕ} (r : Fin 2) (k : Fin (n + 1)) :
    ff3IsDomino (ff3VerticalDomino r k) := by
  refine ⟨?_, ?_⟩
  · simp [ff3VerticalDomino, Fin.ext_iff]
  · intro x hx y hy hxy
    simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · right
      simp
    · right
      simp
    · exact (hxy rfl).elim

theorem ff3_isDomino_iff {n : ℕ} (d : Finset (TilingCell (n + 1))) :
    ff3IsDomino d ↔
      (∃ r : Fin 3, ∃ k : Fin n, d = ff3HorizontalDomino r k) ∨
        ∃ r : Fin 2, ∃ k : Fin (n + 1), d = ff3VerticalDomino r k := by
  constructor
  · rintro ⟨hcard, hadj⟩
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hAdj := hadj x (by simp) y (by simp) hxy
    rcases hAdj with ⟨hrow, hcol⟩ | ⟨hcol, hrow⟩
    · rcases hcol with hxycol | hyxcol
      · left
        let k : Fin n := ⟨x.2.val, by omega⟩
        refine ⟨x.1, k, ?_⟩
        have hx0 : x = (x.1, k.castSucc) := by
          apply Prod.ext
          · rfl
          · rfl
        have hy1 : y = (x.1, k.succ) := by
          apply Prod.ext
          · exact hrow.symm
          · exact Fin.ext hxycol.symm
        rw [hx0, hy1]
        rfl
      · left
        let k : Fin n := ⟨y.2.val, by omega⟩
        refine ⟨y.1, k, ?_⟩
        have hy0 : y = (y.1, k.castSucc) := by
          apply Prod.ext
          · rfl
          · rfl
        have hx1 : x = (y.1, k.succ) := by
          apply Prod.ext
          · exact hrow
          · exact Fin.ext hyxcol.symm
        rw [hx1, hy0, Finset.pair_comm]
        rfl
    · rcases hrow with hxyrow | hyxrow
      · right
        let r : Fin 2 := ⟨x.1.val, by omega⟩
        refine ⟨r, x.2, ?_⟩
        have hx0 : x = (r.castSucc, x.2) := by
          apply Prod.ext
          · rfl
          · rfl
        have hy1 : y = (r.succ, x.2) := by
          apply Prod.ext
          · exact Fin.ext hxyrow.symm
          · exact hcol.symm
        rw [hx0, hy1]
        rfl
      · right
        let r : Fin 2 := ⟨y.1.val, by omega⟩
        refine ⟨r, y.2, ?_⟩
        have hy0 : y = (r.castSucc, y.2) := by
          apply Prod.ext
          · rfl
          · rfl
        have hx1 : x = (r.succ, y.2) := by
          apply Prod.ext
          · exact Fin.ext hyxrow.symm
          · exact hcol
        rw [hx1, hy0, Finset.pair_comm]
        rfl
  · rintro (⟨r, k, rfl⟩ | ⟨r, k, rfl⟩)
    · exact ff3_horizontal_isDomino r k
    · exact ff3_vertical_isDomino r k

theorem ff3_horizontal_injective {n : ℕ} :
    Function.Injective (fun e : Fin 3 × Fin n ↦ ff3HorizontalDomino e.1 e.2) := by
  rintro ⟨r, k⟩ ⟨s, l⟩ h
  change ff3HorizontalDomino r k = ff3HorizontalDomino s l at h
  have h0 : (r, k.castSucc) ∈ ff3HorizontalDomino s l := by
    rw [← h]
    simp [ff3HorizontalDomino]
  have h1 : (r, k.succ) ∈ ff3HorizontalDomino s l := by
    rw [← h]
    simp [ff3HorizontalDomino]
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hrs, hkl⟩ | ⟨hrs, hkl⟩ <;>
    rcases h1 with ⟨_, hkl'⟩ | ⟨_, hkl'⟩
  · omega
  · apply Prod.ext
    · exact Fin.ext hrs
    · exact Fin.ext hkl
  · omega
  · omega

theorem ff3_vertical_injective {n : ℕ} :
    Function.Injective (fun e : Fin 2 × Fin (n + 1) ↦ ff3VerticalDomino e.1 e.2) := by
  rintro ⟨r, k⟩ ⟨s, l⟩ h
  change ff3VerticalDomino r k = ff3VerticalDomino s l at h
  have h0 : (r.castSucc, k) ∈ ff3VerticalDomino s l := by
    rw [← h]
    simp [ff3VerticalDomino]
  have h1 : (r.succ, k) ∈ ff3VerticalDomino s l := by
    rw [← h]
    simp [ff3VerticalDomino]
  simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hrs, hkl⟩ | ⟨hrs, hkl⟩ <;>
    rcases h1 with ⟨hrs', _⟩ | ⟨hrs', _⟩
  · omega
  · apply Prod.ext
    · exact Fin.ext hrs
    · exact Fin.ext hkl
  · omega
  · omega

theorem ff3_horizontal_ne_vertical {n : ℕ} (r : Fin 3) (k : Fin n)
    (s : Fin 2) (j : Fin (n + 1)) :
    ff3HorizontalDomino r k ≠ ff3VerticalDomino s j := by
  intro h
  have h0 : (s.castSucc, j) ∈ ff3HorizontalDomino r k := by
    rw [h]
    simp [ff3VerticalDomino]
  have h1 : (s.succ, j) ∈ ff3HorizontalDomino r k := by
    rw [h]
    simp [ff3VerticalDomino]
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at h0 h1
  rcases h0 with ⟨hsr, _⟩ | ⟨hsr, _⟩ <;>
    rcases h1 with ⟨hsr', _⟩ | ⟨hsr', _⟩ <;> omega

end MetaMathlibExt
