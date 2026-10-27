/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
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

/-! ## Coordinate conversion helpers -/


/-- The cells covered by a DominoTilings.Domino, cast to ℤ coordinates.
    This allows comparison with DominoTilingsZ.Domino.toShape. -/
def cellsZ (d : DominoTilings.Domino) : Set (ℤ × ℤ) :=
  {((d.cell1.1 : ℤ), (d.cell1.2 : ℤ)), ((d.cell2.1 : ℤ), (d.cell2.2 : ℤ))}

/-! ## Conversion from DominoTilings.Domino to DominoTilingsZ.Domino

Note: We use `DominoTilings.Domino.isHorizontal` and `DominoTilings.Domino.isVertical`
from DominoTilings.lean via dot notation (e.g., `d.isHorizontal`). -/


/-- Convert a DominoTilings.Domino to DominoTilingsZ.Domino.
    
    The conversion uses the minimum coordinate as the anchor point:
    - A horizontal domino becomes DominoTilingsZ.Domino.horizontal (min col) row
    - A vertical domino becomes DominoTilingsZ.Domino.vertical col (min row) -/
def toDominoZ (d : DominoTilings.Domino) : DominoTilingsZ.Domino :=
  if d.isHorizontal then
    -- Horizontal: cells differ in first coordinate
    let minCol := min d.cell1.1 d.cell2.1
    DominoTilingsZ.Domino.horizontal (minCol : ℤ) (d.cell1.2 : ℤ)
  else
    -- Vertical: cells differ in second coordinate
    let minRow := min d.cell1.2 d.cell2.2
    DominoTilingsZ.Domino.vertical (d.cell1.1 : ℤ) (minRow : ℤ)

/-! ## Conversion from DominoTilingsZ.Domino to DominoTilings.Domino -/


/-- A DominoTilingsZ.Domino has positive coordinates if all its cells have positive coordinates.
    This is the precondition for converting to DominoTilings.Domino (which uses ℕ coordinates). -/
def hasPositiveCoords : DominoTilingsZ.Domino → Prop
  | .horizontal i j => i ≥ 1 ∧ j ≥ 1
  | .vertical i j => i ≥ 1 ∧ j ≥ 1

end DominoBridge
