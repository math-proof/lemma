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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part14


namespace MetaMathlibExt

theorem ff3_mem_codeEdges_horizontal {n : ℕ} (c : ff3Code ∅ n)
    (r : Fin 3) (k : Fin n) :
    Sum.inl (r, k) ∈ ff3CodeEdges c ↔ r ∈ ff3ProfileRows (c.1 k) := by
  classical
  simp [ff3CodeEdges]

theorem ff3_mem_codeEdges_vertical {n : ℕ} (c : ff3Code ∅ n) (r : Fin 2)
    (j : Fin (n + 1)) :
    Sum.inr (r, j) ∈ ff3CodeEdges c ↔ (c.2 j).1 = some r := by
  classical
  simp [ff3CodeEdges]

theorem ff3_code_adjacent_disjoint {n : ℕ} (c : ff3Code ∅ n) (l k : Fin n)
    (h : l.succ = k.castSucc) :
    Disjoint (ff3ProfileRows (c.1 l)) (ff3ProfileRows (c.1 k)) := by
  have hd := (c.2 l.succ).property.1
  rw [ff3_incoming_succ] at hd
  rw [h, ff3_outgoing_castSucc] at hd
  exact hd

theorem ff3_code_out_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n) (k : Fin n) :
    Disjoint (ff3ProfileRows (c.1 k)) (ff3VerticalRows (c.2 k.castSucc).1) := by
  have hd := (c.2 k.castSucc).property.2.2
  simpa only [ff3_outgoing_castSucc] using hd

theorem ff3_code_in_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n) (k : Fin n) :
    Disjoint (ff3ProfileRows (c.1 k)) (ff3VerticalRows (c.2 k.succ).1) := by
  have hd := (c.2 k.succ).property.2.1
  simpa only [ff3_incoming_succ] using hd

theorem ff3_code_horizontal_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r : Fin 3) (k : Fin n) (s : Fin 2) (j : Fin (n + 1))
    (hr : r ∈ ff3ProfileRows (c.1 k)) (hs : (c.2 j).1 = some s) :
    Disjoint (ff3HorizontalDomino r k) (ff3VerticalDomino s j) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hj : j = k.castSucc := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.castSucc).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_out_vertical_disjoint c k) hr hrv
    · have hj : j = k.castSucc := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.castSucc).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_out_vertical_disjoint c k) hr hrv
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hj : j = k.succ := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.succ).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_in_vertical_disjoint c k) hr hrv
    · have hj : j = k.succ := Fin.ext hcol.symm
      subst j
      have hrv : r ∈ ff3VerticalRows (c.2 k.succ).1 := by
        rw [hs]
        simp [ff3VerticalRows, Fin.ext_iff, hrow]
      exact Finset.disjoint_left.mp (ff3_code_in_vertical_disjoint c k) hr hrv

theorem ff3_code_horizontal_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r s : Fin 3) (k l : Fin n) (hr : r ∈ ff3ProfileRows (c.1 k))
    (hs : s ∈ ff3ProfileRows (c.1 l)) (hne : (r, k) ≠ (s, l)) :
    Disjoint (ff3HorizontalDomino r k) (ff3HorizontalDomino s l) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · apply hne
      exact Prod.ext (Fin.ext hrow) (Fin.ext hcol)
    · have hkl : l.succ = k.castSucc := Fin.ext hcol.symm
      have hd := ff3_code_adjacent_disjoint c l k hkl
      have hrs : r = s := Fin.ext hrow
      subst s
      exact Finset.disjoint_left.mp hd hs hr
  · simp only [ff3HorizontalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at hxs
    rcases hxs with ⟨hrow, hcol⟩ | ⟨hrow, hcol⟩
    · have hkl : k.succ = l.castSucc := Fin.ext hcol
      have hd := ff3_code_adjacent_disjoint c k l hkl
      have hrs : r = s := Fin.ext hrow
      subst s
      exact Finset.disjoint_left.mp hd hr hs
    · apply hne
      exact Prod.ext (Fin.ext hrow) (Fin.ext (Nat.add_right_cancel hcol))

theorem ff3_code_vertical_disjoint {n : ℕ} (c : ff3Code ∅ n)
    (r s : Fin 2) (j l : Fin (n + 1)) (hr : (c.2 j).1 = some r)
    (hs : (c.2 l).1 = some s) (hne : (r, j) ≠ (s, l)) :
    Disjoint (ff3VerticalDomino r j) (ff3VerticalDomino s l) := by
  rw [Finset.disjoint_left]
  intro x hx hxs
  simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hxs
    rcases hxs with ⟨_, hcol⟩ | ⟨_, hcol⟩ <;>
      subst l <;> exact hne (congrArg (fun t ↦ (t, j)) (Option.some.inj (hr.symm.trans hs)))
  · simp only [ff3VerticalDomino, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at hxs
    rcases hxs with ⟨_, hcol⟩ | ⟨_, hcol⟩ <;>
      subst l <;> exact hne (congrArg (fun t ↦ (t, j)) (Option.some.inj (hr.symm.trans hs)))

theorem ff3_codeEdges_isMatching {n : ℕ} (c : ff3Code ∅ n) :
    ff3IsEdgeMatching (ff3CodeEdges c) := by
  intro e he f hf hne
  rcases e with e | e <;> rcases f with f | f
  · exact ff3_code_horizontal_disjoint c e.1 f.1 e.2 f.2
      ((ff3_mem_codeEdges_horizontal c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_horizontal c f.1 f.2).mp hf)
      (fun h ↦ hne (congrArg Sum.inl h))
  · exact ff3_code_horizontal_vertical_disjoint c e.1 e.2 f.1 f.2
      ((ff3_mem_codeEdges_horizontal c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_vertical c f.1 f.2).mp hf)
  · exact Disjoint.symm <| ff3_code_horizontal_vertical_disjoint c f.1 f.2 e.1 e.2
      ((ff3_mem_codeEdges_horizontal c f.1 f.2).mp hf)
      ((ff3_mem_codeEdges_vertical c e.1 e.2).mp he)
  · exact ff3_code_vertical_disjoint c e.1 f.1 e.2 f.2
      ((ff3_mem_codeEdges_vertical c e.1 e.2).mp he)
      ((ff3_mem_codeEdges_vertical c f.1 f.2).mp hf)
      (fun h ↦ hne (congrArg Sum.inr h))

theorem ff3_codeEdges_crosses {n : ℕ} (c : ff3Code ∅ n) :
    ff3CrossesEveryCut (ff3CodeEdges c) := by
  intro k
  obtain ⟨r, hr⟩ := ff3_profileRows_nonempty (c.1 k)
  exact ⟨r, (ff3_mem_codeEdges_horizontal c r k).mpr hr⟩

end MetaMathlibExt
