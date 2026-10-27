/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
import Def.Combinatorics.Tiling.DominoBridge.Part2
open Finset BigOperators

/-!
# Bridge between Domino representations

This module provides equivalence functions between the two Domino representations
used in the project:

1. **WeightedSets.lean** (`DominoTilingsZ.Domino`): Inductive type with `horizontal`/`vertical`
   constructors, using ℤ coordinates, with `Set Domino` for tilings
2. **DominoTilings.lean** (`DominoTilings.Domino`): Structure with `cell1`/`cell2` fields,
   using ℕ coordinates, with `Finset Domino` for tilings

## Design Rationale

The two representations were designed for different purposes:
- **DominoTilingsZ** uses ℤ coordinates for generality in weighted set theory and generating
  function calculations. The inductive type makes pattern matching on orientation natural.
- **DominoTilings** uses ℕ coordinates for finite rectangle tilings and faultfree classification.
  The structure representation is more flexible for adjacency conditions.

For rectangles with positive coordinates (the typical case), the representations are equivalent.
This bridge enables theorem transfer between files when needed.

## Main Definitions

* `DominoBridge.toDominoZ`: Convert a DominoTilings.Domino to DominoTilingsZ.Domino
* `DominoBridge.toDominoN`: Convert a DominoTilingsZ.Domino with positive coordinates to
  DominoTilings.Domino
* `DominoBridge.hasPositiveCoords`: Predicate for DominoTilingsZ.Domino having positive coords
* `DominoBridge.cellsZ`: The cells covered by a DominoTilings.Domino (cast to ℤ coordinates)

## Main Results

* `DominoBridge.toDominoZ_hasPositiveCoords`: Converting from ℕ preserves positivity
* `DominoBridge.toDominoZ_cells`: Converting to ℤ preserves the set of cells
* `DominoBridge.toDominoN_cells`: Converting from ℤ preserves the set of cells

## References

* Source files: `FPS/WeightedSets.lean` (DominoTilingsZ), `Details/DominoTilings.lean` (DominoTilings)

## Tags

domino, tiling, bridge, equivalence
-/


namespace DominoBridge

/-! ## Round-trip properties -/
/-! ## Cell preservation theorems -/


/-- Converting DominoTilings.Domino to DominoTilingsZ.Domino preserves the set of cells (cast to ℤ).
    
    This is the key theorem for theorem transfer between the two representations.
    It shows that the cells covered by a domino are the same regardless of which
    representation is used. -/
theorem toDominoZ_cells (d : DominoTilings.Domino) : (toDominoZ d).toShape = cellsZ d := by
  simp only [toDominoZ, cellsZ]
  split_ifs with hH
  · -- Horizontal case: cells have same row (cell1.2 = cell2.2)
    simp only [DominoTilingsZ.Domino.toShape]
    -- In horizontal case, cells differ in first coordinate
    rcases d.adjacent with ⟨hcol, _⟩ | ⟨hrow, hadj⟩
    · -- Same column contradicts distinct
      exfalso
      have hdist := d.distinct
      have : d.cell1 = d.cell2 := Prod.ext hcol hH
      exact hdist this
    · -- Same row, adjacent columns
      rcases hadj with h1 | h2
      · -- cell1.1 + 1 = cell2.1
        have hmin : min d.cell1.1 d.cell2.1 = d.cell1.1 := by omega
        simp only [hmin, hrow]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
      · -- cell2.1 + 1 = cell1.1
        have hmin : min d.cell1.1 d.cell2.1 = d.cell2.1 := by omega
        simp only [hmin, hrow]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
  · -- Vertical case: cells have same column
    simp only [DominoTilingsZ.Domino.toShape]
    rcases d.adjacent with ⟨hcol, hadj⟩ | ⟨hrow, _⟩
    · -- Same column, adjacent rows
      rcases hadj with h1 | h2
      · -- cell1.2 + 1 = cell2.2
        have hmin : min d.cell1.2 d.cell2.2 = d.cell1.2 := by omega
        simp only [hmin, hcol]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · left; constructor <;> omega
          · right; constructor <;> omega
      · -- cell2.2 + 1 = cell1.2
        have hmin : min d.cell1.2 d.cell2.2 = d.cell2.2 := by omega
        simp only [hmin, hcol]
        ext p
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
        constructor
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
        · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
          · right; constructor <;> omega
          · left; constructor <;> omega
    · -- Same row contradicts not horizontal
      exact absurd hrow hH

end DominoBridge
