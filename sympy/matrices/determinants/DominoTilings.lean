/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib

/-!
# Domino Tilings of Height-3 Rectangles

This file formalizes the classification of faultfree domino tilings of the rectangle R_{n,3}
from Subsection sec.details.domino of the Algebraic Combinatorics notes.

A domino is a 1×2 or 2×1 rectangle. A domino tiling of a rectangle is a partition of the
rectangle's cells into dominos. A fault in a tiling is a vertical line that passes through
the entire rectangle without crossing any domino. A faultfree tiling has no such faults.

## Main definitions

* `Rectangle`: The set of cells in an n×m rectangle
* `Domino`: A pair of adjacent cells (horizontal or vertical)
* `DominoTiling`: A set of dominos that partition a rectangle
* `hasFault`: Whether a tiling has a fault at a given column
* `isFaultfree`: Whether a tiling has no faults
* `TilingA`: The family of faultfree tilings A_n for even n
* `TilingB`: The family of faultfree tilings B_n for even n (reflection of A_n)
* `TilingC`: The unique faultfree tiling of R_{2,3} with no vertical domino in column 1

## Main results

* `faultfree_classification`: The faultfree domino tilings of height-3 rectangles are
  precisely A_2, A_4, A_6, ..., B_2, B_4, B_6, ..., and C.
* `faultfree_top_vertical_classification`: A faultfree tiling with a vertical domino in
  the top two squares of column 1 is equivalent to some A_n.
* `faultfree_bottom_vertical_classification`: A faultfree tiling with a vertical domino
  in the bottom two squares of column 1 is equivalent to some B_n.
* `faultfree_no_vertical_unique`: A faultfree 2×3 tiling with no vertical domino in
  column 1 is equivalent to C (using `TilingEquiv`, not structural equality).

## References

* Source: AlgebraicCombinatorics/tex/Details/DominoTilings.tex
* Grinberg, Darij. "Algebraic Combinatorics" (lecture notes), Subsection sec.gf.weighted-set.domino

## Tags

domino tiling, faultfree, rectangle, combinatorics
-/

open Finset BigOperators

namespace DominoTilings

/-!
## Basic Definitions
-/

/-- A cell in a rectangle, represented as a pair (column, row) with 1-indexing.
    Column numbers go from 1 to n (left to right).
    Row numbers go from 1 to m (bottom to top). -/
abbrev Cell := ℕ × ℕ

/-- The rectangle R_{n,m} is the set of cells {(x, y) : 1 ≤ x ≤ n, 1 ≤ y ≤ m}. -/
def Rectangle (n m : ℕ) : Finset Cell :=
  (Finset.range n ×ˢ Finset.range m).map ⟨fun (x, y) => (x + 1, y + 1), by
    intro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    ext <;> omega⟩

/-- Membership characterization for Rectangle. -/
theorem mem_Rectangle {n m : ℕ} {c : Cell} :
    c ∈ Rectangle n m ↔ c.1 ≥ 1 ∧ c.1 ≤ n ∧ c.2 ≥ 1 ∧ c.2 ≤ m := by
  simp only [Rectangle, Finset.mem_map, Finset.mem_product, Finset.mem_range, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨hx, hy⟩, h⟩
    have : c = (x + 1, y + 1) := h.symm
    simp only [this]
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨c.1 - 1, c.2 - 1, ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · show (c.1 - 1 + 1, c.2 - 1 + 1) = c
      ext <;> omega

/-- A domino is a pair of adjacent cells, either horizontal or vertical. -/
@[ext]
structure Domino where
  /-- The first cell of the domino -/
  cell1 : Cell
  /-- The second cell of the domino -/
  cell2 : Cell
  /-- The cells are distinct -/
  distinct : cell1 ≠ cell2
  /-- The cells are adjacent (horizontally or vertically) -/
  adjacent : (cell1.1 = cell2.1 ∧ (cell1.2 + 1 = cell2.2 ∨ cell2.2 + 1 = cell1.2)) ∨
             (cell1.2 = cell2.2 ∧ (cell1.1 + 1 = cell2.1 ∨ cell2.1 + 1 = cell1.1))
  deriving DecidableEq

namespace Domino

/-- The set of cells covered by a domino. -/
def cells (d : Domino) : Finset Cell := {d.cell1, d.cell2}

/-- Each domino covers exactly 2 cells. -/
@[simp]
/-- A domino is horizontal if both cells are in the same row. -/
def isHorizontal (d : Domino) : Prop := d.cell1.2 = d.cell2.2

/-- A domino is vertical if both cells are in the same column. -/
def isVertical (d : Domino) : Prop := d.cell1.1 = d.cell2.1

instance : DecidablePred isHorizontal := fun d => inferInstanceAs (Decidable (d.cell1.2 = d.cell2.2))
instance : DecidablePred isVertical := fun d => inferInstanceAs (Decidable (d.cell1.1 = d.cell2.1))

/-- The leftmost column touched by a domino. -/
def minCol (d : Domino) : ℕ := min d.cell1.1 d.cell2.1

/-- The rightmost column touched by a domino. -/
def maxCol (d : Domino) : ℕ := max d.cell1.1 d.cell2.1

/-! ### Shifting operations for dominos

These operations shift a domino horizontally by adding or subtracting from the column
coordinate. They are essential for the Fibonacci recurrence bijection on 2×n tilings. -/

/-- Shift a domino k columns to the right. -/
def shiftNat (d : Domino) (k : ℕ) : Domino where
  cell1 := (d.cell1.1 + k, d.cell1.2)
  cell2 := (d.cell2.1 + k, d.cell2.2)
  distinct := by
    intro h
    simp only [Prod.mk.injEq] at h
    exact d.distinct (Prod.ext (by omega) h.2)
  adjacent := by
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · left
      constructor
      · simp only [hcol]
      · rcases hrow with h | h <;> [left; right] <;> omega
    · right
      constructor
      · exact hrow
      · rcases hcol with h | h <;> [left; right] <;> omega

/-- Shift a domino k columns to the left. Requires that both cells have column ≥ k+1. -/
def shiftNeg (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) : Domino where
  cell1 := (d.cell1.1 - k, d.cell1.2)
  cell2 := (d.cell2.1 - k, d.cell2.2)
  distinct := by
    intro h
    simp only [Prod.mk.injEq] at h
    have hdist := d.distinct
    apply hdist
    ext
    · omega
    · exact h.2
  adjacent := by
    rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
    · left
      constructor
      · omega
      · rcases hrow with h | h <;> [left; right] <;> omega
    · right
      constructor
      · exact hrow
      · rcases hcol with h | h <;> [left; right] <;> omega

@[simp]
theorem shiftNat_cell1 (d : Domino) (k : ℕ) : (d.shiftNat k).cell1 = (d.cell1.1 + k, d.cell1.2) := rfl

@[simp]
theorem shiftNat_cell2 (d : Domino) (k : ℕ) : (d.shiftNat k).cell2 = (d.cell2.1 + k, d.cell2.2) := rfl

@[simp]
theorem shiftNeg_cell1 (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    (d.shiftNeg k h1 h2).cell1 = (d.cell1.1 - k, d.cell1.2) := rfl

@[simp]
theorem shiftNeg_cell2 (d : Domino) (k : ℕ) (h1 : d.cell1.1 ≥ k + 1) (h2 : d.cell2.1 ≥ k + 1) :
    (d.shiftNeg k h1 h2).cell2 = (d.cell2.1 - k, d.cell2.2) := rfl

/-- The vertical domino covering column 1 in a 2-row rectangle: cells (1,1) and (1,2). -/
def vertical_1_1 : Domino where
  cell1 := (1, 1)
  cell2 := (1, 2)
  distinct := by decide
  adjacent := Or.inl ⟨rfl, Or.inl rfl⟩

/-- The horizontal domino covering row 1, columns 1-2: cells (1,1) and (2,1). -/
def horizontal_1_1 : Domino where
  cell1 := (1, 1)
  cell2 := (2, 1)
  distinct := by decide
  adjacent := Or.inr ⟨rfl, Or.inl rfl⟩

/-- The horizontal domino covering row 2, columns 1-2: cells (1,2) and (2,2). -/
def horizontal_1_2 : Domino where
  cell1 := (1, 2)
  cell2 := (2, 2)
  distinct := by decide
  adjacent := Or.inr ⟨rfl, Or.inl rfl⟩

@[simp] theorem vertical_1_1_cell1 : vertical_1_1.cell1 = (1, 1) := rfl
@[simp] theorem vertical_1_1_cell2 : vertical_1_1.cell2 = (1, 2) := rfl
@[simp] theorem horizontal_1_1_cell1 : horizontal_1_1.cell1 = (1, 1) := rfl
@[simp] theorem horizontal_1_1_cell2 : horizontal_1_1.cell2 = (2, 1) := rfl
@[simp] theorem horizontal_1_2_cell1 : horizontal_1_2.cell1 = (1, 2) := rfl
@[simp] theorem horizontal_1_2_cell2 : horizontal_1_2.cell2 = (2, 2) := rfl

@[simp] theorem vertical_1_1_isVertical : vertical_1_1.isVertical := rfl
@[simp] theorem horizontal_1_1_isHorizontal : horizontal_1_1.isHorizontal := rfl
@[simp] theorem horizontal_1_2_isHorizontal : horizontal_1_2.isHorizontal := rfl

theorem vertical_1_1_cells : vertical_1_1.cells = {(1, 1), (1, 2)} := rfl
/-- The "flipped" vertical domino with cell1 and cell2 swapped. -/
def vertical_1_1_flip : Domino where
  cell1 := (1, 2)
  cell2 := (1, 1)
  distinct := by decide
  adjacent := Or.inl ⟨rfl, Or.inr rfl⟩

@[simp] theorem vertical_1_1_flip_cell1 : vertical_1_1_flip.cell1 = (1, 2) := rfl
@[simp] theorem vertical_1_1_flip_cell2 : vertical_1_1_flip.cell2 = (1, 1) := rfl

/-- A domino tiling of a rectangle is a finite set of dominos such that:
    1. Each domino's cells are within the rectangle
    2. The dominos partition the rectangle (cover all cells exactly once) -/
structure DominoTiling (n m : ℕ) where
  /-- The set of dominos in the tiling -/
  dominos : Finset Domino
  /-- All dominos are within the rectangle -/
  dominos_in_rect : ∀ d ∈ dominos, d.cells ⊆ Rectangle n m
  /-- The dominos cover all cells -/
  covers_all : (dominos.biUnion Domino.cells) = Rectangle n m
  /-- The dominos are pairwise disjoint -/
  pairwise_disjoint : ∀ d₁ ∈ dominos, ∀ d₂ ∈ dominos, d₁ ≠ d₂ → Disjoint d₁.cells d₂.cells

namespace DominoTiling

variable {n m : ℕ}

/-- Dominos in a tiling have cells with positive column coordinates. -/
theorem domino_cells_col_ge_one (T : DominoTiling n m) (d : Domino) (hd : d ∈ T.dominos) :
    d.cell1.1 ≥ 1 ∧ d.cell2.1 ≥ 1 := by
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
  have hc2 : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h1 := h hc1
  have h2 := h hc2
  rw [mem_Rectangle] at h1 h2
  exact ⟨h1.1, h2.1⟩

/-- In a 2-row tiling with horizontal_1_1 and horizontal_1_2, all other dominos have cells
    with column ≥ 3. This is because horizontal_1_1 and horizontal_1_2 cover all cells
    in columns 1 and 2. -/
theorem other_dominos_col_ge_3 (T : DominoTiling (n + 2) 2)
    (hh1 : horizontal_1_1 ∈ T.dominos) (hh2 : horizontal_1_2 ∈ T.dominos)
    (d : Domino) (hd : d ∈ T.dominos) (hne1 : d ≠ horizontal_1_1) (hne2 : d ≠ horizontal_1_2) :
    d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
  have hdisj1 := T.pairwise_disjoint d hd horizontal_1_1 hh1 hne1
  have hdisj2 := T.pairwise_disjoint d hd horizontal_1_2 hh2 hne2
  have h := domino_cells_col_ge_one T d hd
  constructor
  · by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc1_in_rect := hd_in_rect (Finset.mem_insert_self _ _)
    rw [mem_Rectangle] at hc1_in_rect
    have hrow : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hrow with hr1 | hr2
    · have : d.cell1 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr1]
        · right; ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_self _ _) this
    · have : d.cell1 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr2]
        · right; ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_self _ _) this
  · by_contra hlt
    push Not at hlt
    have hd_in_rect := T.dominos_in_rect d hd
    have hc2_in_rect := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rw [mem_Rectangle] at hc2_in_rect
    have hrow : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hrow with hr1 | hr2
    · have : d.cell2 ∈ horizontal_1_1.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr1]
        · right; ext <;> simp [hc2, hr1]
      exact Finset.disjoint_left.mp hdisj1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this
    · have : d.cell2 ∈ horizontal_1_2.cells := by
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
        have hcol : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
        rcases hcol with hc1 | hc2
        · left; ext <;> simp [hc1, hr2]
        · right; ext <;> simp [hc2, hr2]
      exact Finset.disjoint_left.mp hdisj2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) this

/-- A tiling has a fault at column k if there is a vertical line between columns k and k+1
    that does not cross any domino. Equivalently, no domino spans columns k and k+1. -/
def hasFaultAt (T : DominoTiling n m) (k : ℕ) : Prop :=
  k ≥ 1 ∧ k < n ∧ ∀ d ∈ T.dominos, ¬(d.minCol ≤ k ∧ k < d.maxCol)

instance (T : DominoTiling n m) (k : ℕ) : Decidable (T.hasFaultAt k) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A tiling is faultfree if it has no faults at any column in range [1, n-1]. -/
def isFaultfree (T : DominoTiling n m) : Prop :=
  ∀ k : ℕ, k ≥ 1 → k < n → ¬T.hasFaultAt k

/-- Whether a tiling contains a vertical domino in the top two squares of column c. -/
def hasTopVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c ∧
    ((d.cell1.2 = m - 1 ∧ d.cell2.2 = m) ∨ (d.cell1.2 = m ∧ d.cell2.2 = m - 1))

/-- Whether a tiling contains a vertical domino in the bottom two squares of column c. -/
def hasBottomVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c ∧
    ((d.cell1.2 = 1 ∧ d.cell2.2 = 2) ∨ (d.cell1.2 = 2 ∧ d.cell2.2 = 1))

/-- Whether a tiling contains any vertical domino in column c. -/
def hasVerticalInCol (T : DominoTiling n m) (c : ℕ) : Prop :=
  ∃ d ∈ T.dominos, d.isVertical ∧ d.cell1.1 = c

/-- Two tilings are equivalent if they cover the same cells with the same domino cell sets.

    This is the appropriate notion of equality for tilings, since the Domino structure
    distinguishes between {cell1 := a, cell2 := b} and {cell1 := b, cell2 := a} even
    though they cover the same cells.

    Note: This is a weaker notion than structural equality (T₁ = T₂), but is the
    mathematically correct notion for classification theorems. -/
def TilingEquiv (T₁ T₂ : DominoTiling n m) : Prop :=
  T₁.dominos.image Domino.cells = T₂.dominos.image Domino.cells

/-- Prepend a vertical domino at (1,1)-(1,2) to a tiling of Rectangle n 2,
    creating a tiling of Rectangle (n+1) 2.

    This is one of the inverse maps in the Fibonacci recurrence bijection.
    The vertical domino covers the entire first column, creating a fault at x=1. -/
def prependVertical (T : DominoTiling n 2) : DominoTiling (n + 1) 2 where
  dominos := insert vertical_1_1 (T.dominos.image (fun d => d.shiftNat 1))
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_image] at hd
    rcases hd with rfl | ⟨d', hd', rfl⟩
    · -- Case: d = vertical_1_1
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d is a shifted domino
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · -- c = d'.shiftNat 1.cell1
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
        have h := hd'_in hd'_c1
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell1]
        omega
      · -- c = d'.shiftNat 1.cell2
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h := hd'_in hd'_c2
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell2]
        omega
  covers_all := by
    ext c
    constructor
    · -- Forward: c in union → c in Rectangle (n+1) 2
      intro hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image] at hc
      rcases hc with ⟨d, hd, hc_in_d⟩
      rcases hd with rfl | ⟨d', hd', rfl⟩
      · -- d = vertical_1_1
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d is shifted
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
          have h := hd'_in hd'_c1
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell1]
          omega
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have h := hd'_in hd'_c2
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell2]
          omega
    · -- Backward: c in Rectangle (n+1) 2 → c in union
      intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image]
      -- Case split on column of c
      by_cases hcol : c.1 = 1
      · -- Column 1: covered by vertical_1_1
        use vertical_1_1
        constructor
        · left; rfl
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          -- c.2 ∈ {1, 2} since c ∈ Rectangle (n+1) 2
          have hrow_ge := hc.2.2.1
          have hrow_le := hc.2.2.2
          rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
          · left; ext <;> simp [hcol, hr1.symm]
          · have hr2 : c.2 = 2 := by omega
            right; ext <;> simp [hcol, hr2]
      · -- Column > 1: covered by shifted domino
        have hcol_ge2 : c.1 ≥ 2 := by omega
        -- Find the original cell (c.1 - 1, c.2) in Rectangle n 2
        have hc_orig : (c.1 - 1, c.2) ∈ Rectangle n 2 := by
          rw [mem_Rectangle]
          omega
        -- This cell is covered by some domino in T
        rw [← T.covers_all] at hc_orig
        simp only [Finset.mem_biUnion] at hc_orig
        rcases hc_orig with ⟨d', hd', hc_in_d'⟩
        -- The shifted domino covers c
        use d'.shiftNat 1
        constructor
        · right; exact ⟨d', hd', rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d' ⊢
          rcases hc_in_d' with heq1 | heq2
          · left
            simp only [Domino.shiftNat_cell1]
            have hcol_eq := congrArg Prod.fst heq1
            have hrow_eq := congrArg Prod.snd heq1
            simp at hcol_eq hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
          · right
            simp only [Domino.shiftNat_cell2]
            have hcol_eq := congrArg Prod.fst heq2
            have hrow_eq := congrArg Prod.snd heq2
            simp at hcol_eq hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_image] at hd1 hd2
    rcases hd1 with rfl | ⟨d1', hd1', rfl⟩
    · -- d1 = vertical_1_1
      rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = vertical_1_1 - contradiction
        exact absurd rfl hne
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        -- c1 ∈ vertical_1_1.cells has column 1
        -- c2 ∈ (d2'.shiftNat 1).cells has column ≥ 2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [vertical_1_1_cell1, vertical_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 is shifted
      rcases hd2 with rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = vertical_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [vertical_1_1_cell1, vertical_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- Both are shifted
        -- Need: d1' ≠ d2' (since shifting is injective and d1 ≠ d2)
        have hne' : d1' ≠ d2' := by
          intro heq'
          apply hne
          rw [heq']
        have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
        rw [Finset.disjoint_iff_ne] at hdisj ⊢
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        -- Extract the original cells
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        · -- cell1 vs cell1
          simp only [Domino.shiftNat_cell1, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell1 vs cell2
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
        · -- cell2 vs cell1
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell2 vs cell2
          simp only [Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-- Prepend two horizontal dominos at (1,1)-(2,1) and (1,2)-(2,2) to a tiling of Rectangle n 2,
    creating a tiling of Rectangle (n+2) 2.

    This is one of the inverse maps in the Fibonacci recurrence bijection.
    The two horizontal dominos cover the first two columns, creating a fault at x=2. -/
def prependHorizontalPair (T : DominoTiling n 2) : DominoTiling (n + 2) 2 where
  dominos := insert horizontal_1_1 (insert horizontal_1_2 (T.dominos.image (fun d => d.shiftNat 2)))
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_image] at hd
    rcases hd with rfl | rfl | ⟨d', hd', rfl⟩
    · -- Case: d = horizontal_1_1
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d = horizontal_1_2
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp [mem_Rectangle]
      · simp [mem_Rectangle]
    · -- Case: d is a shifted domino
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · -- c = d'.shiftNat 2.cell1
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
        have h := hd'_in hd'_c1
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell1]
        omega
      · -- c = d'.shiftNat 2.cell2
        have hd'_in := T.dominos_in_rect d' hd'
        have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have h := hd'_in hd'_c2
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNat_cell2]
        omega
  covers_all := by
    ext c
    constructor
    · -- Forward: c in union → c in Rectangle (n+2) 2
      intro hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image] at hc
      rcases hc with ⟨d, hd, hc_in_d⟩
      rcases hd with rfl | rfl | ⟨d', hd', rfl⟩
      · -- d = horizontal_1_1
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d = horizontal_1_2
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · simp [mem_Rectangle]
        · simp [mem_Rectangle]
      · -- d is shifted
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c1 : d'.cell1 ∈ d'.cells := Finset.mem_insert_self _ _
          have h := hd'_in hd'_c1
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell1]
          omega
        · have hd'_in := T.dominos_in_rect d' hd'
          have hd'_c2 : d'.cell2 ∈ d'.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
          have h := hd'_in hd'_c2
          rw [mem_Rectangle] at h ⊢
          simp only [Domino.shiftNat_cell2]
          omega
    · -- Backward: c in Rectangle (n+2) 2 → c in union
      intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image]
      -- Case split on column of c
      rcases Nat.lt_trichotomy c.1 2 with hcol_lt | hcol_eq | hcol_gt
      · -- Column 1: covered by horizontal_1_1 or horizontal_1_2
        have hcol1 : c.1 = 1 := by omega
        have hrow_ge := hc.2.2.1
        have hrow_le := hc.2.2.2
        rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
        · -- Row 1: horizontal_1_1
          use horizontal_1_1
          constructor
          · left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hcol1, hr1.symm]
        · -- Row 2: horizontal_1_2
          have hr2 : c.2 = 2 := by omega
          use horizontal_1_2
          constructor
          · right; left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hcol1, hr2]
      · -- Column 2: covered by horizontal_1_1 or horizontal_1_2
        have hrow_ge := hc.2.2.1
        have hrow_le := hc.2.2.2
        rcases Nat.eq_or_lt_of_le hrow_ge with hr1 | hr_gt
        · -- Row 1: horizontal_1_1
          use horizontal_1_1
          constructor
          · left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hcol_eq, hr1.symm]
        · -- Row 2: horizontal_1_2
          have hr2 : c.2 = 2 := by omega
          use horizontal_1_2
          constructor
          · right; left; rfl
          · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hcol_eq, hr2]
      · -- Column > 2: covered by shifted domino
        have hcol_ge3 : c.1 ≥ 3 := by omega
        -- Find the original cell (c.1 - 2, c.2) in Rectangle n 2
        have hc_orig : (c.1 - 2, c.2) ∈ Rectangle n 2 := by
          rw [mem_Rectangle]
          omega
        -- This cell is covered by some domino in T
        rw [← T.covers_all] at hc_orig
        simp only [Finset.mem_biUnion] at hc_orig
        rcases hc_orig with ⟨d', hd', hc_in_d'⟩
        -- The shifted domino covers c
        use d'.shiftNat 2
        constructor
        · right; right; exact ⟨d', hd', rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d' ⊢
          rcases hc_in_d' with heq1 | heq2
          · left
            simp only [Domino.shiftNat_cell1]
            have hcol_eq' := congrArg Prod.fst heq1
            have hrow_eq := congrArg Prod.snd heq1
            simp at hcol_eq' hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
          · right
            simp only [Domino.shiftNat_cell2]
            have hcol_eq' := congrArg Prod.fst heq2
            have hrow_eq := congrArg Prod.snd heq2
            simp at hcol_eq' hrow_eq
            ext
            · simp; omega
            · simp; exact hrow_eq
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_image] at hd1 hd2
    rcases hd1 with rfl | rfl | ⟨d1', hd1', rfl⟩
    · -- d1 = horizontal_1_1
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1 - contradiction
        exact absurd rfl hne
      · -- d2 = horizontal_1_2
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, horizontal_1_2_cell1,
                     horizontal_1_2_cell2, Prod.mk.injEq] at heq <;>
          omega
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 = horizontal_1_2
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, horizontal_1_2_cell1,
                     horizontal_1_2_cell2, Prod.mk.injEq] at heq <;>
          omega
      · -- d2 = horizontal_1_2 - contradiction
        exact absurd rfl hne
      · -- d2 is shifted
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d2' hd2')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_2_cell1, horizontal_1_2_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
    · -- d1 is shifted
      rcases hd2 with rfl | rfl | ⟨d2', hd2', rfl⟩
      · -- d2 = horizontal_1_1
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_1_cell1, horizontal_1_1_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- d2 = horizontal_1_2
        rw [Finset.disjoint_iff_ne]
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        have hcol := (domino_cells_col_ge_one T d1' hd1')
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        all_goals
          simp only [horizontal_1_2_cell1, horizontal_1_2_cell2, Domino.shiftNat_cell1,
                     Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          omega
      · -- Both are shifted
        have hne' : d1' ≠ d2' := by
          intro heq'
          apply hne
          rw [heq']
        have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
        rw [Finset.disjoint_iff_ne] at hdisj ⊢
        intro c1 hc1 c2 hc2 heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
        rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
        · -- cell1 vs cell1
          simp only [Domino.shiftNat_cell1, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell1 vs cell2
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
        · -- cell2 vs cell1
          simp only [Domino.shiftNat_cell1, Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1 (Finset.mem_insert_self _ _) heq_orig
        · -- cell2 vs cell2
          simp only [Domino.shiftNat_cell2, Prod.mk.injEq] at heq
          have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
          exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-! ### Restriction operations for the Fibonacci recurrence bijection

These operations extract the "rest" of a tiling after removing the dominos
covering the first column(s). They form the forward maps in the bijection:
  Tiling (Rectangle (n+2) 2) ≃ Tiling (Rectangle n 2) ⊕ Tiling (Rectangle (n+1) 2)

The idea:
- If the first column has a vertical domino, remove it and shift remaining by 1
- If the first two columns have horizontal dominos, remove them and shift by 2

Together with prependVertical and prependHorizontalPair, these establish the
Fibonacci recurrence: |Tiling(n+2, 2)| = |Tiling(n, 2)| + |Tiling(n+1, 2)|
-/

/-- If a domino d in a tiling is disjoint from a domino covering {(1,1), (1,2)},
    then d's cells have column ≥ 2. This is the generalized version that works
    with any domino covering the first column, not just vertical_1_1. -/
theorem domino_col_ge_two_of_disjoint_from_first_col (T : DominoTiling (n + 1) 2)
    (v : Domino) (hv : v ∈ T.dominos) (hv_cells : v.cells = vertical_1_1.cells)
    (d : Domino) (hd : d ∈ T.dominos) (hne : d ≠ v) :
    d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
  have hdisj := T.pairwise_disjoint d hd v hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := domino_cells_col_ge_one T d hd
  -- v covers (1,1) and (1,2)
  have hv_11 : (1, 1) ∈ v.cells := by rw [hv_cells]; simp [vertical_1_1_cells]
  have hv_12 : (1, 2) ∈ v.cells := by rw [hv_cells]; simp [vertical_1_1_cells]
  constructor
  · by_contra h
    push Not at h
    have h1 : d.cell1.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [mem_Rectangle] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hrow_bound with hr1 | hr2
    · have heq : d.cell1 = (1, 1) := Prod.ext h1 hr1
      exact hdisj d.cell1 hc1_in_d (1, 1) hv_11 heq
    · have heq : d.cell1 = (1, 2) := Prod.ext h1 hr2
      exact hdisj d.cell1 hc1_in_d (1, 2) hv_12 heq
  · by_contra h
    push Not at h
    have h2 : d.cell2.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [mem_Rectangle] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hrow_bound with hr1 | hr2
    · have heq : d.cell2 = (1, 1) := Prod.ext h2 hr1
      exact hdisj d.cell2 hc2_in_d (1, 1) hv_11 heq
    · have heq : d.cell2 = (1, 2) := Prod.ext h2 hr2
      exact hdisj d.cell2 hc2_in_d (1, 2) hv_12 heq

/-- If a domino d in a tiling containing vertical_1_1 is not vertical_1_1,
    then d's cells have column ≥ 2. -/
theorem domino_col_ge_two_of_ne_vertical (T : DominoTiling (n + 1) 2) (hv : vertical_1_1 ∈ T.dominos)
    (d : Domino) (hd : d ∈ T.dominos) (hne : d ≠ vertical_1_1) :
    d.cell1.1 ≥ 2 ∧ d.cell2.1 ≥ 2 := by
  have hdisj := T.pairwise_disjoint d hd vertical_1_1 hv hne
  rw [Finset.disjoint_iff_ne] at hdisj
  have hcols := domino_cells_col_ge_one T d hd
  constructor
  · by_contra h
    push Not at h
    have h1 : d.cell1.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [mem_Rectangle] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hrow_bound with hr1 | hr2
    · have heq : d.cell1 = (1, 1) := Prod.ext h1 hr1
      have hv_c1 : vertical_1_1.cell1 ∈ vertical_1_1.cells := Finset.mem_insert_self _ _
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell1 hv_c1 (by simp [heq])
    · have heq : d.cell1 = (1, 2) := Prod.ext h1 hr2
      have hv_c2 : vertical_1_1.cell2 ∈ vertical_1_1.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact hdisj d.cell1 hc1_in_d vertical_1_1.cell2 hv_c2 (by simp [heq])
  · by_contra h
    push Not at h
    have h2 : d.cell2.1 = 1 := by omega
    have hd_in := T.dominos_in_rect d hd
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [mem_Rectangle] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hrow_bound with hr1 | hr2
    · have heq : d.cell2 = (1, 1) := Prod.ext h2 hr1
      have hv_c1 : vertical_1_1.cell1 ∈ vertical_1_1.cells := Finset.mem_insert_self _ _
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell1 hv_c1 (by simp [heq])
    · have heq : d.cell2 = (1, 2) := Prod.ext h2 hr2
      have hv_c2 : vertical_1_1.cell2 ∈ vertical_1_1.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact hdisj d.cell2 hc2_in_d vertical_1_1.cell2 hv_c2 (by simp [heq])

/-- Extract the tiling of Rectangle n 2 from a tiling of Rectangle (n+1) 2
    that has vertical_1_1 as its first domino.

    This removes vertical_1_1 and shifts all remaining dominos one column left.
    It is the left inverse of prependVertical. -/
def restrictAfterVertical (T : DominoTiling (n + 1) 2) (hv : vertical_1_1 ∈ T.dominos) :
    DominoTiling n 2 where
  dominos := (T.dominos.erase vertical_1_1).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hcols := domino_col_ge_two_of_ne_vertical T hv d (Finset.mem_of_mem_erase hd) hd'.1
    d.shiftNeg 1 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_ne := (Finset.mem_erase.mp hd_erase).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase
    have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_ne := (Finset.mem_erase.mp hd_erase).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase
      have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      -- The cell (c.1 + 1, c.2) is in Rectangle (n+1) 2 and is covered by some domino
      have hc_orig : (c.1 + 1, c.2) ∈ Rectangle (n + 1) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      -- d cannot be vertical_1_1 since (c.1+1, c.2) has column ≥ 2
      have hd_ne : d ≠ vertical_1_1 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          vertical_1_1_cell1, vertical_1_1_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
          omega
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_erase : d ∈ T.dominos.erase vertical_1_1 := Finset.mem_erase.mpr ⟨hd_ne, hd_mem⟩
      have hcols := domino_col_ge_two_of_ne_vertical T hv d hd_mem hd_ne
      use d.shiftNeg 1 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1 hd2
    obtain ⟨d1', hd1'_erase, rfl⟩ := hd1
    obtain ⟨d2', hd2'_erase, rfl⟩ := hd2
    have hd1'_ne := (Finset.mem_erase.mp hd1'_erase).1
    have hd2'_ne := (Finset.mem_erase.mp hd2'_erase).1
    have hd1'_mem := Finset.mem_of_mem_erase hd1'_erase
    have hd2'_mem := Finset.mem_of_mem_erase hd2'_erase
    have hcols1 := domino_col_ge_two_of_ne_vertical T hv d1' hd1'_mem hd1'_ne
    have hcols2 := domino_col_ge_two_of_ne_vertical T hv d2' hd2'_mem hd2'_ne
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1' hd1'_mem d2' hd2'_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · -- cell1 vs cell1
      simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell1 vs cell2
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · -- cell2 vs cell1
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell2 vs cell2
      simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-- Extract the tiling of Rectangle n 2 from a tiling of Rectangle (n+2) 2
    that has horizontal_1_1 and horizontal_1_2 as its first dominos.

    This removes the two horizontal dominos and shifts remaining dominos two columns left.
    It is the left inverse of prependHorizontalPair. -/
def restrictAfterHorizontalPair (T : DominoTiling (n + 2) 2)
    (hh1 : horizontal_1_1 ∈ T.dominos) (hh2 : horizontal_1_2 ∈ T.dominos) :
    DominoTiling n 2 where
  dominos := ((T.dominos.erase horizontal_1_1).erase horizontal_1_2).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
    let hcols := other_dominos_col_ge_3 T hh1 hh2 d (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
    d.shiftNeg 2 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_erase2 := Finset.mem_of_mem_erase hd_erase
    have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
    have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase2
    have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_erase2 := Finset.mem_of_mem_erase hd_erase
      have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
      have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase2
      have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      -- The cell (c.1 + 2, c.2) is in Rectangle (n+2) 2 and is covered by some domino
      have hc_orig : (c.1 + 2, c.2) ∈ Rectangle (n + 2) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      -- d cannot be horizontal_1_1 or horizontal_1_2 since (c.1+2, c.2) has column ≥ 3
      have hd_ne1 : d ≠ horizontal_1_1 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          horizontal_1_1_cell1, horizontal_1_1_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_ne2 : d ≠ horizontal_1_2 := by
        intro heq
        subst heq
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton,
          horizontal_1_2_cell1, horizontal_1_2_cell2] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_erase1 : d ∈ T.dominos.erase horizontal_1_1 := Finset.mem_erase.mpr ⟨hd_ne1, hd_mem⟩
      have hd_erase : d ∈ (T.dominos.erase horizontal_1_1).erase horizontal_1_2 :=
        Finset.mem_erase.mpr ⟨hd_ne2, hd_erase1⟩
      have hcols := other_dominos_col_ge_3 T hh1 hh2 d hd_mem hd_ne1 hd_ne2
      use d.shiftNeg 2 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1 hd2
    obtain ⟨d1', hd1'_erase, rfl⟩ := hd1
    obtain ⟨d2', hd2'_erase, rfl⟩ := hd2
    have hd1'_erase2 := Finset.mem_of_mem_erase hd1'_erase
    have hd2'_erase2 := Finset.mem_of_mem_erase hd2'_erase
    have hd1'_ne2 := (Finset.mem_erase.mp hd1'_erase).1
    have hd2'_ne2 := (Finset.mem_erase.mp hd2'_erase).1
    have hd1'_ne1 := (Finset.mem_erase.mp hd1'_erase2).1
    have hd2'_ne1 := (Finset.mem_erase.mp hd2'_erase2).1
    have hd1'_mem := Finset.mem_of_mem_erase hd1'_erase2
    have hd2'_mem := Finset.mem_of_mem_erase hd2'_erase2
    have hcols1 := other_dominos_col_ge_3 T hh1 hh2 d1' hd1'_mem hd1'_ne1 hd1'_ne2
    have hcols2 := other_dominos_col_ge_3 T hh1 hh2 d2' hd2'_mem hd2'_ne1 hd2'_ne2
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1' hd1'_mem d2' hd2'_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · -- cell1 vs cell1
      simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell1 vs cell2
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · -- cell2 vs cell1
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell2 vs cell2
      simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-! ### Bijection lemmas for the Fibonacci recurrence

These lemmas establish that prependVertical/prependHorizontalPair and
restrictAfterVertical/restrictAfterHorizontalPair are inverse operations. -/

/-- In a 2×(n+1) tiling, cell (1,1) is covered by some domino. -/
theorem exists_domino_covering_11 (T : DominoTiling (n + 1) 2) :
    ∃ d ∈ T.dominos, (1, 1) ∈ d.cells := by
  have h11 : (1, 1) ∈ Rectangle (n + 1) 2 := by
    rw [mem_Rectangle]
    omega
  rw [← T.covers_all] at h11
  simp only [Finset.mem_biUnion] at h11
  exact h11

/-- Any domino covering cell (1,1) in a 2×(n+2) tiling has cells = {(1,1), (1,2)} or {(1,1), (2,1)}. -/
theorem domino_covering_11_cells (T : DominoTiling (n + 2) 2) (d : Domino) (hd : d ∈ T.dominos)
    (hcov : (1, 1) ∈ d.cells) : d.cells = {(1, 1), (1, 2)} ∨ d.cells = {(1, 1), (2, 1)} := by
  have hd_in := T.dominos_in_rect d hd
  have hc1_in := hd_in (Finset.mem_insert_self _ _)
  have hc2_in := hd_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [mem_Rectangle] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hcov
  rcases d.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
  · left
    rcases hcov with heq | heq
    · have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_1 : d.cell2.1 = 1 := by omega
      rcases hrow with h | h
      · have hc2_2 : d.cell2.2 = 2 := by omega
        have hc2 : d.cell2 = (1, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_1 : d.cell1.1 = 1 := by omega
      rcases hrow with h | h
      · omega
      · have hc1_2 : d.cell1.2 = 2 := by omega
        have hc1 : d.cell1 = (1, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]
  · right
    rcases hcov with heq | heq
    · have hc1_1 : d.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d.cell1.2 = 1 := congrArg Prod.snd heq.symm
      have hc2_2 : d.cell2.2 = 1 := by omega
      rcases hcol with h | h
      · have hc2_1 : d.cell2.1 = 2 := by omega
        have hc2 : d.cell2 = (2, 1) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d.cell2.2 = 1 := congrArg Prod.snd heq.symm
      have hc1_2 : d.cell1.2 = 1 := by omega
      rcases hcol with h | h
      · omega
      · have hc1_1 : d.cell1.1 = 2 := by omega
        have hc1 : d.cell1 = (2, 1) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]

/-- If a domino in a 2×(n+2) tiling covers (1,1) with a horizontal domino (cells = {(1,1), (2,1)}),
    then there must be another domino covering (1,2). -/
theorem exists_domino_covering_12_of_horizontal (T : DominoTiling (n + 2) 2) (d : Domino)
    (hd : d ∈ T.dominos) (hcells : d.cells = {(1, 1), (2, 1)}) :
    ∃ d' ∈ T.dominos, d' ≠ d ∧ (1, 2) ∈ d'.cells := by
  have h12 : (1, 2) ∈ Rectangle (n + 2) 2 := by rw [mem_Rectangle]; omega
  rw [← T.covers_all] at h12
  simp only [Finset.mem_biUnion] at h12
  obtain ⟨d', hd'_mem, hd'_cov⟩ := h12
  use d'
  refine ⟨hd'_mem, ?_, hd'_cov⟩
  intro heq
  subst heq
  rw [hcells] at hd'_cov
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hd'_cov
  rcases hd'_cov with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- The second domino covering (1,2) when the first covers {(1,1), (2,1)} must cover {(1,2), (2,2)}. -/
theorem domino_covering_12_cells (T : DominoTiling (n + 2) 2) (d d' : Domino)
    (hd : d ∈ T.dominos) (hd' : d' ∈ T.dominos) (hne : d' ≠ d)
    (hd_cells : d.cells = {(1, 1), (2, 1)}) (hd'_cov : (1, 2) ∈ d'.cells) :
    d'.cells = {(1, 2), (2, 2)} := by
  have hdisj := T.pairwise_disjoint d' hd' d hd hne
  have hd'_not_11 : (1, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h11_in_d : (1, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (1, 1) h (1, 1) h11_in_d rfl
  have hd'_not_21 : (2, 1) ∉ d'.cells := by
    intro h
    rw [Finset.disjoint_iff_ne] at hdisj
    have h21_in_d : (2, 1) ∈ d.cells := by rw [hd_cells]; simp
    exact hdisj (2, 1) h (2, 1) h21_in_d rfl
  have hd'_in := T.dominos_in_rect d' hd'
  have hc1_in := hd'_in (Finset.mem_insert_self _ _)
  have hc2_in := hd'_in (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  rw [mem_Rectangle] at hc1_in hc2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd'_cov
  rcases d'.adjacent with ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩
  · -- d' is vertical
    rcases hd'_cov with heq | heq
    · have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_1 : d'.cell2.1 = 1 := by omega
      rcases hrow with h | h
      · omega
      · have hc2_2 : d'.cell2.2 = 1 := by omega
        have hc2 : d'.cell2 = (1, 1) := Prod.ext hc2_1 hc2_2
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          right; exact hc2.symm
        exact absurd h11_in_d' hd'_not_11
    · have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_1 : d'.cell1.1 = 1 := by omega
      rcases hrow with h | h
      · have hc1_2' : d'.cell1.2 = 1 := by omega
        have hc1 : d'.cell1 = (1, 1) := Prod.ext hc1_1 hc1_2'
        have h11_in_d' : (1, 1) ∈ d'.cells := by
          simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          left; exact hc1.symm
        exact absurd h11_in_d' hd'_not_11
      · omega
  · -- d' is horizontal
    rcases hd'_cov with heq | heq
    · have hc1_1 : d'.cell1.1 = 1 := congrArg Prod.fst heq.symm
      have hc1_2 : d'.cell1.2 = 2 := congrArg Prod.snd heq.symm
      have hc2_2 : d'.cell2.2 = 2 := by omega
      rcases hcol with h | h
      · have hc2_1 : d'.cell2.1 = 2 := by omega
        have hc2 : d'.cell2 = (2, 2) := Prod.ext hc2_1 hc2_2
        simp only [Domino.cells, heq.symm, hc2]
      · omega
    · have hc2_1 : d'.cell2.1 = 1 := congrArg Prod.fst heq.symm
      have hc2_2 : d'.cell2.2 = 2 := congrArg Prod.snd heq.symm
      have hc1_2 : d'.cell1.2 = 2 := by omega
      rcases hcol with h | h
      · omega
      · have hc1_1 : d'.cell1.1 = 2 := by omega
        have hc1 : d'.cell1 = (2, 2) := Prod.ext hc1_1 hc1_2
        simp only [Domino.cells, hc1, heq.symm, Finset.pair_comm]

/-! ### Generalized restrict functions

These functions generalize `restrictAfterVertical` and `restrictAfterHorizontalPair` to work
with any domino having the appropriate cells, not just the specific canonical dominos.
This is needed for the Equiv construction since tilings may use flipped versions of dominos. -/

/-- Generalized version of restrictAfterVertical that works with any domino v
    having cells = {(1,1), (1,2)}. -/
def restrictAfterVerticalGen (T : DominoTiling (n + 1) 2) (v : Domino)
    (hv : v ∈ T.dominos) (hv_cells : v.cells = vertical_1_1.cells) :
    DominoTiling n 2 where
  dominos := (T.dominos.erase v).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d
                   (Finset.mem_of_mem_erase hd) hd'.1
    d.shiftNeg 1 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_ne := (Finset.mem_erase.mp hd_erase).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase
    have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_ne := (Finset.mem_erase.mp hd_erase).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase
      have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      have hc_orig : (c.1 + 1, c.2) ∈ Rectangle (n + 1) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      have hd_ne : d ≠ v := by
        intro heq
        subst heq
        rw [hv_cells] at hc_in_d
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with heq | heq
        · have h1 := congrArg Prod.fst heq; simp at h1; omega
        · have h1 := congrArg Prod.fst heq; simp at h1; omega
      have hd_erase : d ∈ T.dominos.erase v := Finset.mem_erase.mpr ⟨hd_ne, hd_mem⟩
      have hcols := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d hd_mem hd_ne
      use d.shiftNeg 1 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1 hd2
    obtain ⟨d1', hd1'_erase, rfl⟩ := hd1
    obtain ⟨d2', hd2'_erase, rfl⟩ := hd2
    have hd1'_ne := (Finset.mem_erase.mp hd1'_erase).1
    have hd2'_ne := (Finset.mem_erase.mp hd2'_erase).1
    have hd1'_mem := Finset.mem_of_mem_erase hd1'_erase
    have hd2'_mem := Finset.mem_of_mem_erase hd2'_erase
    have hcols1 := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d1' hd1'_mem hd1'_ne
    have hcols2 := domino_col_ge_two_of_disjoint_from_first_col T v hv hv_cells d2' hd2'_mem hd2'_ne
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1' hd1'_mem d2' hd2'_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell1 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell1 (Finset.mem_insert_self _ _) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell1 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1'.cell2 = d2'.cell2 := by ext <;> omega
      exact hdisj d1'.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2'.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-- Lemma: other dominos have column ≥ 3 when two dominos cover the first two columns. -/
theorem other_dominos_col_ge_3_gen (T : DominoTiling (n + 2) 2) (d1 d2 : Domino)
    (hd1 : d1 ∈ T.dominos) (hd2 : d2 ∈ T.dominos)
    (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset Cell))
    (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset Cell))
    (d : Domino) (hd : d ∈ T.dominos) (hne1 : d ≠ d1) (hne2 : d ≠ d2) :
    d.cell1.1 ≥ 3 ∧ d.cell2.1 ≥ 3 := by
  have hdisj1 := T.pairwise_disjoint d hd d1 hd1 hne1
  have hdisj2 := T.pairwise_disjoint d hd d2 hd2 hne2
  rw [Finset.disjoint_iff_ne] at hdisj1 hdisj2
  have hcols := domino_cells_col_ge_one T d hd
  -- d1 covers (1,1) and (2,1), d2 covers (1,2) and (2,2)
  have h11 : (1, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h21 : (2, 1) ∈ d1.cells := by rw [hd1_cells]; simp
  have h12 : (1, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have h22 : (2, 2) ∈ d2.cells := by rw [hd2_cells]; simp
  have hd_in := T.dominos_in_rect d hd
  constructor
  · by_contra h
    push Not at h
    have hc1_col : d.cell1.1 = 1 ∨ d.cell1.1 = 2 := by omega
    have hc1_in_d : d.cell1 ∈ d.cells := Finset.mem_insert_self _ _
    have hc1_in_rect := hd_in hc1_in_d
    rw [mem_Rectangle] at hc1_in_rect
    have hrow_bound : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
    rcases hc1_col with hcol1 | hcol2 <;> rcases hrow_bound with hr1 | hr2
    · have heq : d.cell1 = (1, 1) := Prod.ext hcol1 hr1
      exact hdisj1 d.cell1 hc1_in_d (1, 1) h11 heq
    · have heq : d.cell1 = (1, 2) := Prod.ext hcol1 hr2
      exact hdisj2 d.cell1 hc1_in_d (1, 2) h12 heq
    · have heq : d.cell1 = (2, 1) := Prod.ext hcol2 hr1
      exact hdisj1 d.cell1 hc1_in_d (2, 1) h21 heq
    · have heq : d.cell1 = (2, 2) := Prod.ext hcol2 hr2
      exact hdisj2 d.cell1 hc1_in_d (2, 2) h22 heq
  · by_contra h
    push Not at h
    have hc2_col : d.cell2.1 = 1 ∨ d.cell2.1 = 2 := by omega
    have hc2_in_d : d.cell2 ∈ d.cells := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have hc2_in_rect := hd_in hc2_in_d
    rw [mem_Rectangle] at hc2_in_rect
    have hrow_bound : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
    rcases hc2_col with hcol1 | hcol2 <;> rcases hrow_bound with hr1 | hr2
    · have heq : d.cell2 = (1, 1) := Prod.ext hcol1 hr1
      exact hdisj1 d.cell2 hc2_in_d (1, 1) h11 heq
    · have heq : d.cell2 = (1, 2) := Prod.ext hcol1 hr2
      exact hdisj2 d.cell2 hc2_in_d (1, 2) h12 heq
    · have heq : d.cell2 = (2, 1) := Prod.ext hcol2 hr1
      exact hdisj1 d.cell2 hc2_in_d (2, 1) h21 heq
    · have heq : d.cell2 = (2, 2) := Prod.ext hcol2 hr2
      exact hdisj2 d.cell2 hc2_in_d (2, 2) h22 heq

/-- Generalized version of restrictAfterHorizontalPair that works with any dominos d1, d2
    having the appropriate cells. -/
def restrictAfterHorizontalPairGen (T : DominoTiling (n + 2) 2) (d1 d2 : Domino)
    (hd1 : d1 ∈ T.dominos) (hd2 : d2 ∈ T.dominos)
    (hd1_cells : d1.cells = ({(1, 1), (2, 1)} : Finset Cell))
    (hd2_cells : d2.cells = ({(1, 2), (2, 2)} : Finset Cell)) :
    DominoTiling n 2 where
  dominos := ((T.dominos.erase d1).erase d2).attach.image fun ⟨d, hd⟩ =>
    let hd' := Finset.mem_erase.mp hd
    let hd'' := Finset.mem_erase.mp (Finset.mem_of_mem_erase hd)
    let hcols := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d
                   (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hd)) hd''.1 hd'.1
    d.shiftNeg 2 hcols.1 hcols.2
  dominos_in_rect := by
    intro d' hd'
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd'
    obtain ⟨d, hd_erase, rfl⟩ := hd'
    have hd_erase2 := Finset.mem_of_mem_erase hd_erase
    have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
    have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
    have hd_mem := Finset.mem_of_mem_erase hd_erase2
    have hcols := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d hd_mem hd_ne1 hd_ne2
    intro c hc
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
    have hd_in_rect := T.dominos_in_rect d hd_mem
    rcases hc with rfl | rfl
    · have h := hd_in_rect (Finset.mem_insert_self _ _)
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell1]
      omega
    · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rw [mem_Rectangle] at h ⊢
      simp only [Domino.shiftNeg_cell2]
      omega
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists] at hc
      obtain ⟨d', ⟨d, hd_erase, rfl⟩, hc_in_d'⟩ := hc
      have hd_erase2 := Finset.mem_of_mem_erase hd_erase
      have hd_ne2 := (Finset.mem_erase.mp hd_erase).1
      have hd_ne1 := (Finset.mem_erase.mp hd_erase2).1
      have hd_mem := Finset.mem_of_mem_erase hd_erase2
      have hcols := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d hd_mem hd_ne1 hd_ne2
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d'
      have hd_in_rect := T.dominos_in_rect d hd_mem
      rcases hc_in_d' with rfl | rfl
      · have h := hd_in_rect (Finset.mem_insert_self _ _)
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell1]
        omega
      · have h := hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        rw [mem_Rectangle] at h ⊢
        simp only [Domino.shiftNeg_cell2]
        omega
    · intro hc
      rw [mem_Rectangle] at hc
      simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_attach, true_and,
        Subtype.exists]
      -- The cell (c.1 + 2, c.2) is in Rectangle (n+2) 2 and is covered by some domino
      have hc_orig : (c.1 + 2, c.2) ∈ Rectangle (n + 2) 2 := by
        rw [mem_Rectangle]
        omega
      rw [← T.covers_all] at hc_orig
      simp only [Finset.mem_biUnion] at hc_orig
      obtain ⟨d, hd_mem, hc_in_d⟩ := hc_orig
      -- d cannot be d1 or d2 since (c.1+2, c.2) has column ≥ 3
      have hd_ne1' : d ≠ d1 := by
        intro heq
        subst heq
        rw [hd1_cells] at hc_in_d
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_ne2' : d ≠ d2 := by
        intro heq
        subst heq
        rw [hd2_cells] at hc_in_d
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with heq | heq
        · have := congrArg Prod.fst heq
          simp at this
        · have := congrArg Prod.fst heq
          simp at this
          omega
      have hd_erase1 : d ∈ T.dominos.erase d1 := Finset.mem_erase.mpr ⟨hd_ne1', hd_mem⟩
      have hd_erase : d ∈ (T.dominos.erase d1).erase d2 :=
        Finset.mem_erase.mpr ⟨hd_ne2', hd_erase1⟩
      have hcols := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d hd_mem hd_ne1' hd_ne2'
      use d.shiftNeg 2 hcols.1 hcols.2
      constructor
      · use d, hd_erase
      · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d ⊢
        rcases hc_in_d with heq | heq
        · left
          simp only [Domino.shiftNeg_cell1]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
        · right
          simp only [Domino.shiftNeg_cell2]
          have hcol_eq := congrArg Prod.fst heq
          have hrow_eq := congrArg Prod.snd heq
          simp at hcol_eq hrow_eq
          ext <;> simp <;> omega
  pairwise_disjoint := by
    intro d1' hd1' d2' hd2' hne
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at hd1' hd2'
    obtain ⟨d1'', hd1''_erase, rfl⟩ := hd1'
    obtain ⟨d2'', hd2''_erase, rfl⟩ := hd2'
    have hd1''_erase2 := Finset.mem_of_mem_erase hd1''_erase
    have hd2''_erase2 := Finset.mem_of_mem_erase hd2''_erase
    have hd1''_ne2 := (Finset.mem_erase.mp hd1''_erase).1
    have hd2''_ne2 := (Finset.mem_erase.mp hd2''_erase).1
    have hd1''_ne1 := (Finset.mem_erase.mp hd1''_erase2).1
    have hd2''_ne1 := (Finset.mem_erase.mp hd2''_erase2).1
    have hd1''_mem := Finset.mem_of_mem_erase hd1''_erase2
    have hd2''_mem := Finset.mem_of_mem_erase hd2''_erase2
    have hcols1 := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d1'' hd1''_mem hd1''_ne1 hd1''_ne2
    have hcols2 := other_dominos_col_ge_3_gen T d1 d2 hd1 hd2 hd1_cells hd2_cells d2'' hd2''_mem hd2''_ne1 hd2''_ne2
    have hne' : d1'' ≠ d2'' := by
      intro heq
      apply hne
      subst heq
      rfl
    have hdisj := T.pairwise_disjoint d1'' hd1''_mem d2'' hd2''_mem hne'
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
    rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl
    · -- cell1 vs cell1
      simp only [Domino.shiftNeg_cell1, Prod.mk.injEq] at heq
      have heq_orig : d1''.cell1 = d2''.cell1 := by ext <;> omega
      exact hdisj d1''.cell1 (Finset.mem_insert_self _ _) d2''.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell1 vs cell2
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1''.cell1 = d2''.cell2 := by ext <;> omega
      exact hdisj d1''.cell1 (Finset.mem_insert_self _ _) d2''.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig
    · -- cell2 vs cell1
      simp only [Domino.shiftNeg_cell1, Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1''.cell2 = d2''.cell1 := by ext <;> omega
      exact hdisj d1''.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2''.cell1
        (Finset.mem_insert_self _ _) heq_orig
    · -- cell2 vs cell2
      simp only [Domino.shiftNeg_cell2, Prod.mk.injEq] at heq
      have heq_orig : d1''.cell2 = d2''.cell2 := by ext <;> omega
      exact hdisj d1''.cell2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) d2''.cell2
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) heq_orig

/-! ### Predicate for vertical first column

A tiling has a "vertical first column" if some domino covers cells (1,1) and (1,2).
This is the key predicate for the Fibonacci recurrence bijection. -/

/-- A tiling has a vertical first column if some domino covers cells (1,1) and (1,2). -/
def hasVerticalFirstColumn (T : DominoTiling (n + 2) 2) : Prop :=
  ∃ d ∈ T.dominos, d.cells = ({(1, 1), (1, 2)} : Finset Cell)

instance (T : DominoTiling (n + 2) 2) : Decidable (hasVerticalFirstColumn T) := by
  unfold hasVerticalFirstColumn
  infer_instance

/-- The dichotomy: every 2×(n+2) tiling either has a vertical first column or a horizontal pair. -/
theorem hasVerticalFirstColumn_or_horizontalPair (T : DominoTiling (n + 2) 2) :
    hasVerticalFirstColumn T ∨
    (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
    (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
  obtain ⟨d, hd_mem, hd_cov⟩ := exists_domino_covering_11 T
  rcases domino_covering_11_cells T d hd_mem hd_cov with hvert | hhoriz
  · left
    exact ⟨d, hd_mem, hvert⟩
  · right
    constructor
    · exact ⟨d, hd_mem, hhoriz⟩
    · obtain ⟨d', hd'_mem, hd'_ne, hd'_cov⟩ := exists_domino_covering_12_of_horizontal T d hd_mem hhoriz
      exact ⟨d', hd'_mem, domino_covering_12_cells T d d' hd_mem hd'_mem hd'_ne hhoriz hd'_cov⟩

/-- If a tiling doesn't have a vertical first column, then it has a horizontal pair. -/
theorem horizontalPair_of_not_hasVerticalFirstColumn (T : DominoTiling (n + 2) 2)
    (hnotvert : ¬hasVerticalFirstColumn T) :
    (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
    (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
  rcases hasVerticalFirstColumn_or_horizontalPair T with hvert | hhoriz
  · exact absurd hvert hnotvert
  · exact hhoriz

/-- Forward map for the Fibonacci recurrence bijection.
    Maps a 2×(n+2) tiling to either:
    - `inl T'` where T' is a 2×n tiling (horizontal case)
    - `inr T'` where T' is a 2×(n+1) tiling (vertical case) -/
noncomputable def tiling_2_to_sum (T : DominoTiling (n + 2) 2) :
    (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2) :=
  if hv : hasVerticalFirstColumn T then
    -- Vertical case: there's a domino covering (1,1) and (1,2)
    let v := Classical.choose hv
    let hv_spec := Classical.choose_spec hv
    let hv_mem := hv_spec.1
    let hv_cells := hv_spec.2
    Sum.inr (restrictAfterVerticalGen T v hv_mem hv_cells)
  else
    -- Horizontal case: there are dominos covering (1,1)-(2,1) and (1,2)-(2,2)
    let hpair := horizontalPair_of_not_hasVerticalFirstColumn T hv
    let d1 := Classical.choose hpair.1
    let hd1_spec := Classical.choose_spec hpair.1
    let hd1_mem := hd1_spec.1
    let hd1_cells := hd1_spec.2
    let d2 := Classical.choose hpair.2
    let hd2_spec := Classical.choose_spec hpair.2
    let hd2_mem := hd2_spec.1
    let hd2_cells := hd2_spec.2
    Sum.inl (restrictAfterHorizontalPairGen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells)

/-- Backward map for the Fibonacci recurrence bijection.
    Maps a sum to a 2×(n+2) tiling by prepending dominos. -/
def tiling_2_from_sum : (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2) → DominoTiling (n + 2) 2 :=
  Sum.elim prependHorizontalPair prependVertical

/-- Helper to construct a horizontal domino at position (x, y) extending right.
    The domino covers cells (x, y) and (x+1, y). -/
def mkHorizontalDomino (x y : ℕ) : Domino where
  cell1 := (x, y)
  cell2 := (x + 1, y)
  distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
  adjacent := by right; constructor; rfl; left; rfl

/-- Helper to construct a vertical domino at position (x, y) extending up.
    The domino covers cells (x, y) and (x, y+1). -/
def mkVerticalDomino (x y : ℕ) : Domino where
  cell1 := (x, y)
  cell2 := (x, y + 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; constructor; rfl; left; rfl

/-! ### Simp lemmas for mkHorizontalDomino and mkVerticalDomino -/

@[simp]
/-- The basement dominos for tiling A_n: horizontal dominos filling the bottom row. -/
def basementDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2)).map ⟨fun i =>
    { cell1 := (2 * i + 1, 1)
      cell2 := (2 * i + 2, 1)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩

/-- The left wall for tiling A_n: vertical domino in column 1, rows 2-3. -/
def leftWall : Domino where
  cell1 := (1, 2)
  cell2 := (1, 3)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inl rfl⟩

/-- The right wall for tiling A_n: vertical domino in column n, rows 2-3. -/
def rightWall (n : ℕ) : Domino where
  cell1 := (n, 2)
  cell2 := (n, 3)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inl rfl⟩

/-- The middle dominos for tiling A_n: horizontal dominos in row 2 (except first/last columns). -/
def middleDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 2)
      cell2 := (2 * i + 3, 2)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩

/-- The top dominos for tiling A_n: horizontal dominos in row 3 (except first/last columns). -/
def topDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 3)
      cell2 := (2 * i + 3, 3)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩

/-- Tiling A_n for even positive n ≥ 2.

    This is the faultfree tiling of R_{n,3} with:
    - A vertical domino (left wall) in the top two squares of column 1
    - Horizontal basement dominos filling the bottom row
    - Horizontal middle and top dominos filling the interior
    - A vertical domino (right wall) in the top two squares of column n

    (def.gf.weighted-set.domino.Rn3.ABC (a)) -/
def TilingA (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) : DominoTiling n 3 where
  dominos := basementDominos n ∪ {leftWall} ∪ {rightWall n} ∪
             middleDominos n ∪ topDominos n
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_union, Finset.mem_singleton] at hd
    rcases hd with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominos n
      simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 1, 1) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 2, 1) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
            have : i + 1 ≤ n / 2 := hi
            omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
    · -- d = leftWall
      subst hd
      intro c hc
      simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d = rightWall n
      subst hd
      intro c hc
      simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d ∈ middleDominos n
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
    · -- d ∈ topDominos n
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 2, 3) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 3) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion]
    constructor
    · -- c in biUnion → c in Rectangle (from dominos_in_rect)
      rintro ⟨d, hd_mem, hc_in_d⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
      rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
      · -- d ∈ basementDominos n
        simp only [basementDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 1, 1) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 2, 1) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
              have : i + 1 ≤ n / 2 := hi
              omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
      · -- d = leftWall
        subst hd
        simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d = rightWall n
        subst hd
        simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
      · -- d ∈ topDominos n
        simp only [topDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 3) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 3) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
    · -- c in Rectangle → c in biUnion
      intro hc
      rw [mem_Rectangle] at hc
      obtain ⟨hcol_ge, hcol_le, hrow_ge, hrow_le⟩ := hc
      have hrow : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      rcases hrow with hrow1 | hrow2 | hrow3
      · -- c.2 = 1: covered by basementDominos
        -- Find i such that c.1 ∈ {2i+1, 2i+2}
        have hcol_range : ∃ i < n / 2, c.1 = 2 * i + 1 ∨ c.1 = 2 * i + 2 := by
          use (c.1 - 1) / 2
          constructor
          · obtain ⟨k, hk⟩ := hn; subst hk
            have h2 : c.1 - 1 < 2 * k := by omega
            have : (c.1 - 1) / 2 < k := Nat.div_lt_of_lt_mul h2
            have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
            omega
          · have hmod : (c.1 - 1) % 2 = 0 ∨ (c.1 - 1) % 2 = 1 := by omega
            rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
        obtain ⟨i, hi, hcol_eq⟩ := hcol_range
        -- The basement domino at index i contains c
        use { cell1 := (2 * i + 1, 1), cell2 := (2 * i + 2, 1),
              distinct := by simp,
              adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
        constructor
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; left
          simp only [basementDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          exact ⟨i, hi, rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          rcases hcol_eq with hcol | hcol
          · left; ext <;> simp [hrow1, hcol]
          · right; ext <;> simp [hrow1, hcol]
      · -- c.2 = 2: covered by leftWall, rightWall, or middleDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWall
          use leftWall
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hrow2, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWall
            use rightWall n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              left; ext <;> simp [heq, hrow2]
          · -- 1 < c.1 < n: covered by middleDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 2), cell2 := (2 * i + 3, 2),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; right
              simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow2, hcol]
              · right; ext <;> simp [hrow2, hcol]
      · -- c.2 = 3: covered by leftWall, rightWall, or topDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWall
          use leftWall
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hrow3, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWall
            use rightWall n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              right; ext <;> simp [heq, hrow3]
          · -- 1 < c.1 < n: covered by topDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 3), cell2 := (2 * i + 3, 3),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              right
              simp only [topDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow3, hcol]
              · right; ext <;> simp [hrow3, hcol]
  pairwise_disjoint := by
    intro d₁ hd₁ d₂ hd₂ hne
    simp only [Finset.mem_union, Finset.mem_singleton] at hd₁ hd₂
    -- Case analysis on which component d₁ and d₂ come from
    -- Components: basementDominos, {leftWall}, {rightWall n}, middleDominos, topDominos
    rcases hd₁ with ((((hd₁_base | hd₁_left) | hd₁_right) | hd₁_mid) | hd₁_top) <;>
    rcases hd₂ with ((((hd₂_base | hd₂_left) | hd₂_right) | hd₂_mid) | hd₂_top)
    -- Case 1: basement vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base hd₂_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 2: basement vs leftWall (row 1 vs rows 2,3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 3: basement vs rightWall (row 1 vs rows 2,3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 4: basement vs middleDominos (row 1 vs row 2)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 5: basement vs topDominos (row 1 vs row 3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 6: leftWall vs basement (symmetric to case 2)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 7: leftWall vs leftWall (same element, contradicts hne)
    · subst hd₁_left hd₂_left; exact (hne rfl).elim
    -- Case 8: leftWall vs rightWall (column 1 vs column n)
    · subst hd₁_left hd₂_right
      simp only [Domino.cells, leftWall, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 9: leftWall vs middleDominos (column 1 vs columns 2+)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 10: leftWall vs topDominos (column 1 vs columns 2+)
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 11: rightWall vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 12: rightWall vs leftWall
    · subst hd₁_right hd₂_left
      simp only [Domino.cells, leftWall, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 13: rightWall vs rightWall
    · subst hd₁_right hd₂_right; exact (hne rfl).elim
    -- Case 14: rightWall vs middleDominos (column n vs columns ≤n-1)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_mid
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 15: rightWall vs topDominos (column n vs columns ≤n-1)
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_top
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 16: middleDominos vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 17: middleDominos vs leftWall
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 18: middleDominos vs rightWall
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_mid
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 19: middleDominos vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 20: middleDominos vs topDominos (row 2 vs row 3)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 21: topDominos vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 22: topDominos vs leftWall
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 23: topDominos vs rightWall
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_top
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 24: topDominos vs middleDominos
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 25: topDominos vs topDominos
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega

/-!
### Definition of Tiling B_n (def.gf.weighted-set.domino.Rn3.ABC (b))

B_n is the reflection of A_n across the horizontal axis of symmetry of R_{n,3}.
This swaps row 1 with row 3, keeping row 2 fixed.

For B_n, we have:
- Basement dominos in row 3: horizontal dominos {(2i-1, 3), (2i, 3)} for i ∈ [n/2]
- Left wall: vertical domino {(1, 1), (1, 2)} in the bottom of column 1
- Right wall: vertical domino {(n, 1), (n, 2)} in the bottom of column n
- Middle dominos in row 2: horizontal dominos {(2i, 2), (2i+1, 2)} for i ∈ [n/2-1]
- Bottom dominos in row 1: horizontal dominos {(2i, 1), (2i+1, 1)} for i ∈ [n/2-1]
-/

/-- The "basement" dominos for tiling B_n: horizontal dominos filling row 3 (the top row).
    Named "basement" by analogy with A_n, though in B_n these are at the top due to reflection. -/
def basementDominosB (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2)).map ⟨fun i =>
    { cell1 := (2 * i + 1, 3)
      cell2 := (2 * i + 2, 3)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩

/-- The left wall for tiling B_n: vertical domino in column 1, rows 1-2.
    Note: cell ordering matches reflectDomino3 applied to leftWall. -/
def leftWallB : Domino where
  cell1 := (1, 2)
  cell2 := (1, 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inr rfl⟩

/-- The right wall for tiling B_n: vertical domino in column n, rows 1-2.
    Note: cell ordering matches reflectDomino3 applied to rightWall. -/
def rightWallB (n : ℕ) : Domino where
  cell1 := (n, 2)
  cell2 := (n, 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inr rfl⟩

/-- The bottom dominos for tiling B_n: horizontal dominos in row 1 (except first/last columns). -/
def bottomDominosB (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 1)
      cell2 := (2 * i + 3, 1)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩

/-- Tiling B_n for even positive n ≥ 2.

    This is the reflection of A_n across the horizontal axis.
    It has a vertical domino in the bottom two squares of column 1.

    (def.gf.weighted-set.domino.Rn3.ABC (b)) -/
def TilingB (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) : DominoTiling n 3 where
  dominos := basementDominosB n ∪ {leftWallB} ∪ {rightWallB n} ∪
             middleDominos n ∪ bottomDominosB n
  dominos_in_rect := by
    intro d hd c hc_in_d
    simp only [Finset.mem_union, Finset.mem_singleton] at hd
    rcases hd with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominosB n (row 3)
      simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 1, 3) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 2, 3) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
            have : i + 1 ≤ n / 2 := hi
            omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
    · -- d = leftWallB (rows 1-2, column 1)
      subst hd
      simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      rcases hc_in_d with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d = rightWallB n (rows 1-2, column n)
      subst hd
      simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      rcases hc_in_d with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d ∈ middleDominos n (row 2)
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
    · -- d ∈ bottomDominosB n (row 1)
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 2, 1) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 1) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion]
    constructor
    · -- c in biUnion → c in Rectangle (from dominos_in_rect)
      rintro ⟨d, hd_mem, hc_in_d⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
      rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
      · -- d ∈ basementDominosB n
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 1, 3) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 2, 3) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
              have : i + 1 ≤ n / 2 := hi
              omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
      · -- d = leftWallB
        subst hd
        simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d = rightWallB n
        subst hd
        simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
      · -- d ∈ bottomDominosB n
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 1) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 1) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
    · -- c in Rectangle → c in biUnion
      intro hc
      rw [mem_Rectangle] at hc
      obtain ⟨hcol_ge, hcol_le, hrow_ge, hrow_le⟩ := hc
      have hrow : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      rcases hrow with hrow1 | hrow2 | hrow3
      · -- c.2 = 1: covered by leftWallB, rightWallB, or bottomDominosB
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWallB
          use leftWallB
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hrow1, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWallB
            use rightWallB n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              right; ext <;> simp [heq, hrow1]
          · -- 1 < c.1 < n: covered by bottomDominosB
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 1), cell2 := (2 * i + 3, 1),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              right
              simp only [bottomDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow1, hcol]
              · right; ext <;> simp [hrow1, hcol]
      · -- c.2 = 2: covered by leftWallB, rightWallB, or middleDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWallB
          use leftWallB
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hrow2, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWallB
            use rightWallB n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              left; ext <;> simp [heq, hrow2]
          · -- 1 < c.1 < n: covered by middleDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 2), cell2 := (2 * i + 3, 2),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; right
              simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow2, hcol]
              · right; ext <;> simp [hrow2, hcol]
      · -- c.2 = 3: covered by basementDominosB
        have hcol_range : ∃ i < n / 2, c.1 = 2 * i + 1 ∨ c.1 = 2 * i + 2 := by
          use (c.1 - 1) / 2
          constructor
          · obtain ⟨k, hk⟩ := hn; subst hk
            have h2 : c.1 - 1 < 2 * k := by omega
            have : (c.1 - 1) / 2 < k := Nat.div_lt_of_lt_mul h2
            have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
            omega
          · have hmod : (c.1 - 1) % 2 = 0 ∨ (c.1 - 1) % 2 = 1 := by omega
            rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
        obtain ⟨i, hi, hcol_eq⟩ := hcol_range
        use { cell1 := (2 * i + 1, 3), cell2 := (2 * i + 2, 3),
              distinct := by simp,
              adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
        constructor
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; left
          simp only [basementDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          exact ⟨i, hi, rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          rcases hcol_eq with hcol | hcol
          · left; ext <;> simp [hrow3, hcol]
          · right; ext <;> simp [hrow3, hcol]
  pairwise_disjoint := by
    intro d₁ hd₁ d₂ hd₂ hne
    simp only [Finset.mem_union, Finset.mem_singleton] at hd₁ hd₂
    -- Components: basementDominosB, {leftWallB}, {rightWallB n}, middleDominos, bottomDominosB
    rcases hd₁ with ((((hd₁_base | hd₁_left) | hd₁_right) | hd₁_mid) | hd₁_bot) <;>
    rcases hd₂ with ((((hd₂_base | hd₂_left) | hd₂_right) | hd₂_mid) | hd₂_bot)
    -- Case 1: basementB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base hd₂_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 2: basementB vs leftWallB (row 3 vs rows 1,2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 3: basementB vs rightWallB (row 3 vs rows 1,2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 4: basementB vs middleDominos (row 3 vs row 2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 5: basementB vs bottomB (row 3 vs row 1)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 6: leftWallB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 7: leftWallB vs leftWallB
    · subst hd₁_left hd₂_left; exact (hne rfl).elim
    -- Case 8: leftWallB vs rightWallB
    · subst hd₁_left hd₂_right
      simp only [Domino.cells, leftWallB, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 9: leftWallB vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 10: leftWallB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 11: rightWallB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 12: rightWallB vs leftWallB
    · subst hd₁_right hd₂_left
      simp only [Domino.cells, leftWallB, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 13: rightWallB vs rightWallB
    · subst hd₁_right hd₂_right; exact (hne rfl).elim
    -- Case 14: rightWallB vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_mid
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 15: rightWallB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_bot
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 16: middleDominos vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 17: middleDominos vs leftWallB
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 18: middleDominos vs rightWallB
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_mid
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 19: middleDominos vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 20: middleDominos vs bottomB (row 2 vs row 1)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 21: bottomB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 22: bottomB vs leftWallB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 23: bottomB vs rightWallB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_bot
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 24: bottomB vs middleDominos
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 25: bottomB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega

/-!
### Definition of Tiling C (def.gf.weighted-set.domino.Rn3.ABC (c))

C is the unique faultfree tiling of R_{2,3} consisting of three horizontal dominos.
-/

/-- Tiling C: three horizontal dominos covering R_{2,3}.

    The dominos are:
    - {(1, 1), (2, 1)} (bottom row)
    - {(1, 2), (2, 2)} (middle row)
    - {(1, 3), (2, 3)} (top row)

    (def.gf.weighted-set.domino.Rn3.ABC (c)) -/
def TilingC : DominoTiling 2 3 where
  dominos := {
    { cell1 := (1, 1), cell2 := (2, 1),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ },
    { cell1 := (1, 2), cell2 := (2, 2),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ },
    { cell1 := (1, 3), cell2 := (2, 3),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
  }
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
    · intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> rw [mem_Rectangle] <;> simp
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Domino.cells]
    constructor
    · intro ⟨d, hd_mem, hc⟩
      rcases hd_mem with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl <;> rw [mem_Rectangle] <;> decide
    · intro hc
      rw [mem_Rectangle] at hc
      have h1 : c.1 = 1 ∨ c.1 = 2 := by omega
      have h2 : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      obtain ⟨c1, c2⟩ := c
      simp only at h1 h2 hc
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl | rfl
      · use ⟨(1, 1), (2, 1), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; left; rfl; simp
      · use ⟨(1, 2), (2, 2), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; left; rfl; simp
      · use ⟨(1, 3), (2, 3), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; right; rfl; simp
      · use ⟨(1, 1), (2, 1), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; left; rfl; simp
      · use ⟨(1, 2), (2, 2), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; left; rfl; simp
      · use ⟨(1, 3), (2, 3), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; right; rfl; simp
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd1 hd2
    rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl <;>
      try exact absurd rfl hne
    all_goals (simp only [Domino.cells]; rw [Finset.disjoint_iff_ne]; decide)

/-!
## Horizontal Reflection for Height-3 Tilings

We define reflection across the horizontal axis of R_{n,3}, which swaps rows 1 and 3
while keeping row 2 fixed. This is used to relate TilingA and TilingB.
-/

/-- Reflect a cell across the horizontal midline of a height-3 rectangle.
    Maps (x, 1) ↔ (x, 3) and fixes (x, 2). -/
def reflectCell3 (c : Cell) : Cell := (c.1, 4 - c.2)

/-- Helper lemma for nat subtraction injectivity. -/
theorem nat_sub_inj_4 {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) (h : 4 - a = 4 - b) : a = b := by
  omega

/-- For a domino in Rectangle n 3, cell1 has row ≤ 3. -/
theorem domino_cell1_row_le' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell1.2 ≤ 3 := by
  have h : d.cell1 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.2

/-- For a domino in Rectangle n 3, cell2 has row ≤ 3. -/
theorem domino_cell2_row_le' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell2.2 ≤ 3 := by
  have h : d.cell2 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.2

/-- Reflect a domino in a height-3 rectangle. -/
def reflectDomino3 (d : Domino) (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) : Domino where
  cell1 := reflectCell3 d.cell1
  cell2 := reflectCell3 d.cell2
  distinct := by
    simp only [reflectCell3, ne_eq, Prod.mk.injEq, not_and]
    intro hcol hsub
    have hdist := d.distinct
    apply hdist
    ext
    · exact hcol
    · exact nat_sub_inj_4 (by omega : d.cell1.2 ≤ 4) (by omega : d.cell2.2 ≤ 4) hsub
  adjacent := by
    simp only [reflectCell3]
    rcases d.adjacent with ⟨hcol, hor⟩ | ⟨hrow, hor⟩
    · left
      constructor
      · exact hcol
      · rcases hor with h | h
        · right; omega
        · left; omega
    · right
      constructor
      · omega
      · exact hor

/-- Injectivity lemma for reflectDomino3. -/
theorem reflectDomino3_injective {d1 d2 : Domino}
    (h1a : d1.cell1.2 ≤ 3) (h1b : d1.cell2.2 ≤ 3)
    (h2a : d2.cell1.2 ≤ 3) (h2b : d2.cell2.2 ≤ 3)
    (heq : reflectDomino3 d1 h1a h1b = reflectDomino3 d2 h2a h2b) : d1 = d2 := by
  simp only [reflectDomino3, Domino.mk.injEq, reflectCell3, Prod.mk.injEq] at heq
  ext <;> omega

/-- Reflecting a cell in Rectangle n 3 stays in Rectangle n 3. -/
theorem reflectCell3_mem_Rectangle' {n : ℕ} {c : Cell} (hc : c ∈ Rectangle n 3) :
    reflectCell3 c ∈ Rectangle n 3 := by
  rw [mem_Rectangle] at hc ⊢
  simp only [reflectCell3]
  omega

/-- Reflecting a domino's cells gives the image under reflectCell3. -/
theorem reflectDomino3_cells {d : Domino} (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).cells = d.cells.image reflectCell3 := by
  simp only [Domino.cells, reflectDomino3, Finset.image_insert, Finset.image_singleton]

/-- Reflected domino stays in rectangle. -/
theorem reflectDomino3_cells_subset {n : ℕ} {d : Domino}
    (hd : d.cells ⊆ Rectangle n 3) (h1 : d.cell1.2 ≤ 3) (h2 : d.cell2.2 ≤ 3) :
    (reflectDomino3 d h1 h2).cells ⊆ Rectangle n 3 := by
  intro c hc
  rw [reflectDomino3_cells] at hc
  simp only [Finset.mem_image] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact reflectCell3_mem_Rectangle' (hd hc')

/-- reflectCell3 is injective on Rectangle n 3. -/
theorem reflectCell3_injective_on_rect {n : ℕ} {c1 c2 : Cell}
    (hc1 : c1 ∈ Rectangle n 3) (hc2 : c2 ∈ Rectangle n 3)
    (heq : reflectCell3 c1 = reflectCell3 c2) : c1 = c2 := by
  rw [mem_Rectangle] at hc1 hc2
  simp only [reflectCell3, Prod.mk.injEq] at heq
  ext <;> omega

/-- reflectCell3 is surjective on Rectangle n 3. -/
theorem reflectCell3_surjective_on_rect {n : ℕ} {c : Cell}
    (hc : c ∈ Rectangle n 3) : ∃ c' ∈ Rectangle n 3, reflectCell3 c' = c := by
  rw [mem_Rectangle] at hc
  use (c.1, 4 - c.2)
  constructor
  · rw [mem_Rectangle]
    simp only
    omega
  · simp only [reflectCell3]
    ext <;> omega

/-- Reflect a tiling of R_{n,3} across the horizontal axis.
    This operation is well-defined and produces a valid tiling. -/
noncomputable def reflectTiling3 {n : ℕ} (T : DominoTiling n 3) : DominoTiling n 3 where
  dominos := T.dominos.attach.map ⟨fun ⟨d, hd⟩ =>
    reflectDomino3 d
      (domino_cell1_row_le' (T.dominos_in_rect d hd))
      (domino_cell2_row_le' (T.dominos_in_rect d hd)),
    by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only [Subtype.mk.injEq]
      exact reflectDomino3_injective _ _ _ _ hab⟩
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    exact reflectDomino3_cells_subset (T.dominos_in_rect d' hd') _ _
  covers_all := by
    ext c
    constructor
    · intro hc
      simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_attach, true_and,
        Subtype.exists, ← Function.Embedding.toFun_eq_coe] at hc
      obtain ⟨d, ⟨d', hd', rfl⟩, hc_in_d⟩ := hc
      rw [reflectDomino3_cells] at hc_in_d
      simp only [Finset.mem_image] at hc_in_d
      obtain ⟨c', hc', rfl⟩ := hc_in_d
      have hc'_rect : c' ∈ Rectangle n 3 := T.dominos_in_rect d' hd' hc'
      exact reflectCell3_mem_Rectangle' hc'_rect
    · intro hc
      -- c is in Rectangle n 3, need to show it's covered by some reflected domino
      -- Find c' such that reflectCell3 c' = c
      obtain ⟨c', hc'_rect, hc'_eq⟩ := reflectCell3_surjective_on_rect hc
      -- c' is covered by some domino d' in T
      rw [← T.covers_all] at hc'_rect
      simp only [Finset.mem_biUnion] at hc'_rect
      obtain ⟨d', hd', hc'_in_d'⟩ := hc'_rect
      -- The reflected domino covers c
      simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_attach, true_and,
        Subtype.exists, ← Function.Embedding.toFun_eq_coe]
      use reflectDomino3 d' (domino_cell1_row_le' (T.dominos_in_rect d' hd'))
                           (domino_cell2_row_le' (T.dominos_in_rect d' hd'))
      constructor
      · exact ⟨d', hd', rfl⟩
      · rw [reflectDomino3_cells]
        simp only [Finset.mem_image]
        exact ⟨c', hc'_in_d', hc'_eq⟩
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd1 hd2
    obtain ⟨d1', hd1', rfl⟩ := hd1
    obtain ⟨d2', hd2', rfl⟩ := hd2
    -- d1' ≠ d2' (since reflectDomino3 is injective)
    have hne' : d1' ≠ d2' := by
      intro heq
      apply hne
      subst heq
      rfl
    -- Use the disjointness of d1' and d2' in T
    have hdisj := T.pairwise_disjoint d1' hd1' d2' hd2' hne'
    -- reflectDomino3 preserves disjointness
    rw [reflectDomino3_cells, reflectDomino3_cells]
    rw [Finset.disjoint_iff_ne] at hdisj ⊢
    intro c1 hc1 c2 hc2 heq
    simp only [Finset.mem_image] at hc1 hc2
    obtain ⟨c1', hc1', rfl⟩ := hc1
    obtain ⟨c2', hc2', rfl⟩ := hc2
    -- reflectCell3 c1' = reflectCell3 c2' implies c1' = c2'
    have hc1'_rect : c1' ∈ Rectangle n 3 := T.dominos_in_rect d1' hd1' hc1'
    have hc2'_rect : c2' ∈ Rectangle n 3 := T.dominos_in_rect d2' hd2' hc2'
    have heq' := reflectCell3_injective_on_rect hc1'_rect hc2'_rect heq
    exact hdisj c1' hc1' c2' hc2' heq'

