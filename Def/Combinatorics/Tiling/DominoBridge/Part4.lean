/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
import Theorem.Combinatorics.Tiling.DominoBridge.Part2
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

section TilingEquivalence

variable {n m : ℕ}

/-- Convert a DominoTiling to a Tiling. -/
def toTilingZ (T : DominoTilings.DominoTiling n m) : 
    DominoTilingsZ.Tiling (DominoTilingsZ.Rectangle n m) where
  dominos := dominoFinsetToSet T.dominos
  pairwise_disjoint := toDominoZ_pairwise_disjoint T
  cover := toDominoZ_cover T

/-! ### Dominos in a Tiling of a rectangle have positive coordinates -/

end TilingEquivalence
end DominoBridge
