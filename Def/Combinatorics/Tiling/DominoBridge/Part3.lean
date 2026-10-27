/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
import Theorem.Combinatorics.Tiling.DominoBridge
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

/-! ## Canonical form for DominoTilings.Domino 

The DominoTilings.Domino type allows the two cells to be in either order. For a canonical
representation, we define a form where cell1 is always the "smaller" cell. -/


/-- A DominoTilings.Domino is in canonical form if cell1 is the "smaller" cell:
    - For horizontal dominos: cell1 has smaller column
    - For vertical dominos: cell1 has smaller row -/
def isCanonical (d : DominoTilings.Domino) : Prop :=
  if d.isHorizontal then d.cell1.1 < d.cell2.1
  else d.cell1.2 < d.cell2.2

/-- Swap the cells of a DominoTilings.Domino. -/
def swap (d : DominoTilings.Domino) : DominoTilings.Domino where
  cell1 := d.cell2
  cell2 := d.cell1
  distinct := d.distinct.symm
  adjacent := by
    rcases d.adjacent with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1.symm, h2.symm⟩
    · right; exact ⟨h1.symm, h2.symm⟩

/-- Convert a DominoTilings.Domino to canonical form. -/
def toCanonical (d : DominoTilings.Domino) : DominoTilings.Domino :=
  if d.isHorizontal then
    if d.cell1.1 < d.cell2.1 then d else swap d
  else
    if d.cell1.2 < d.cell2.2 then d else swap d

/-! ## Rectangle correspondence

The two Rectangle definitions use different types:
- `DominoTilings.Rectangle n m : Finset (ℕ × ℕ)` - finite set of natural number pairs
- `DominoTilingsZ.Rectangle n m : Set (ℤ × ℤ)` - set of integer pairs

We establish that they correspond under the natural embedding ℕ → ℤ. -/


/-- Cast a cell from ℕ × ℕ to ℤ × ℤ. -/
def cellToZ (c : ℕ × ℕ) : ℤ × ℤ := (c.1, c.2)

/-! ## Documentation: Relationship between representations

### Key differences between the two Domino types:

| Aspect | DominoTilingsZ.Domino | DominoTilings.Domino |
|--------|------------------------|-------------------------|
| Coordinates | ℤ × ℤ | ℕ × ℕ |
| Representation | Inductive (horizontal/vertical) | Structure (cell1, cell2) |
| Anchor | Explicit position parameter | Implicit via cells |
| Orientation | Explicit in constructor | Derived from cell positions |

### When to use each representation:

- **DominoTilingsZ**: Use when working with generating functions, weighted sets, or when
  you need to pattern match on orientation. The ℤ coordinates allow for translations
  that may temporarily go negative.

- **DominoTilings**: Use when working with finite tilings of rectangles, especially when
  you need to reason about cell membership in finsets. The structure representation
  is more flexible for adjacency conditions.

### Bridging tilings:

To bridge between `DominoTilingsZ.Tiling S` and `DominoTilings.DominoTiling n m`, use:
1. `toDominoZ` / `toDominoN` for individual domino conversion
2. `toDominoZ_cells` / `toDominoN_cells` for cell preservation
3. `rectangle_correspondence` for shape correspondence
-/
/-! ## Tiling equivalence infrastructure

We develop the machinery to convert between `DominoTilings.DominoTiling n m` and
`DominoTilingsZ.Tiling (Rectangle n m)`. This requires:
1. Converting the set of dominos (Finset vs Set)
2. Preserving the disjointness property
3. Preserving the covering property
-/


section TilingEquivalence

variable {n m : ℕ}

/-! ### Converting a DominoTiling to a Tiling -/


/-- Convert a Finset of DominoTilings.Domino to a Set of DominoTilingsZ.Domino. -/
def dominoFinsetToSet (ds : Finset DominoTilings.Domino) : Set DominoTilingsZ.Domino :=
  {toDominoZ d | d ∈ ds}

end TilingEquivalence
end DominoBridge
