/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
import Instance.Combinatorics.Tiling.DominoBridge
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

/-- Convert a DominoTilingsZ.Domino with positive coordinates to DominoTilings.Domino.
    
    The conversion preserves the cells covered by the domino:
    - A horizontal domino at (i, j) becomes a DominoTilings.Domino with cells (i, j) and (i+1, j)
    - A vertical domino at (i, j) becomes a DominoTilings.Domino with cells (i, j) and (i, j+1) -/
def toDominoN (d : DominoTilingsZ.Domino) (hpos : hasPositiveCoords d) : DominoTilings.Domino :=
  match d, hpos with
  | .horizontal i j, ⟨hi, hj⟩ =>
    { cell1 := (i.toNat, j.toNat)
      cell2 := ((i + 1).toNat, j.toNat)
      distinct := by
        simp only [ne_eq, Prod.mk.injEq, not_and]
        intro h
        omega
      adjacent := by
        right
        constructor
        · rfl
        · left; omega }
  | .vertical i j, ⟨hi, hj⟩ =>
    { cell1 := (i.toNat, j.toNat)
      cell2 := (i.toNat, (j + 1).toNat)
      distinct := by
        simp only [ne_eq, Prod.mk.injEq, not_and]
        intro _
        omega
      adjacent := by
        left
        constructor
        · rfl
        · left; omega }

end DominoBridge
