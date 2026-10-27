/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
import Def.Combinatorics.Tiling.DominoBridge.Part3
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

/-- Converting a DominoTiling preserves pairwise disjointness. -/
theorem toDominoZ_pairwise_disjoint (T : DominoTilings.DominoTiling n m) :
    Set.PairwiseDisjoint (dominoFinsetToSet T.dominos) DominoTilingsZ.Domino.toShape := by
  intro dz1 hdz1 dz2 hdz2 hne
  simp only [dominoFinsetToSet, Set.mem_ofPred_eq] at hdz1 hdz2
  obtain ⟨d1, hd1, rfl⟩ := hdz1
  obtain ⟨d2, hd2, rfl⟩ := hdz2
  -- Use that d1 ≠ d2 (since the cells would overlap otherwise)
  have hd1d2 : d1 ≠ d2 := by
    intro heq
    subst heq
    exact hne rfl
  -- Get disjointness from the original tiling
  have hdisj := T.pairwise_disjoint d1 hd1 d2 hd2 hd1d2
  -- Convert to the Z representation using cell preservation
  simp only [Function.onFun, Set.disjoint_left]
  intro x hx1 hx2
  rw [toDominoZ_cells] at hx1
  rw [toDominoZ_cells] at hx2
  simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff] at hx1 hx2
  -- x is in cellsZ d1 and cellsZ d2, which contradicts disjointness
  -- Case analysis on which cells x corresponds to
  rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
  rcases hx1 with hx1_c1 | hx1_c2
  · -- x corresponds to d1.cell1
    rcases hx2 with hx2_c1 | hx2_c2
    · -- x corresponds to d2.cell1
      simp only [Prod.ext_iff] at hx1_c1 hx2_c1
      have hcell : d1.cell1 = d2.cell1 := by ext <;> omega
      have hmem : d1.cell1 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
    · -- x corresponds to d2.cell2
      simp only [Prod.ext_iff] at hx1_c1 hx2_c2
      have hcell : d1.cell1 = d2.cell2 := by ext <;> omega
      have hmem : d1.cell1 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
  · -- x corresponds to d1.cell2
    rcases hx2 with hx2_c1 | hx2_c2
    · -- x corresponds to d2.cell1
      simp only [Prod.ext_iff] at hx1_c2 hx2_c1
      have hcell : d1.cell2 = d2.cell1 := by ext <;> omega
      have hmem : d1.cell2 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem
    · -- x corresponds to d2.cell2
      simp only [Prod.ext_iff] at hx1_c2 hx2_c2
      have hcell : d1.cell2 = d2.cell2 := by ext <;> omega
      have hmem : d1.cell2 ∈ d1.cells ∩ d2.cells := by
        simp only [DominoTilings.Domino.cells, Finset.mem_inter]
        simp [hcell]
      simp [hdisj] at hmem

/-- Converting a DominoTiling preserves the covering property. -/
theorem toDominoZ_cover (T : DominoTilings.DominoTiling n m) :
    ⋃ d ∈ dominoFinsetToSet T.dominos, d.toShape = DominoTilingsZ.Rectangle n m := by
  ext ⟨x, y⟩
  simp only [Set.mem_iUnion, dominoFinsetToSet, Set.mem_ofPred_eq, 
             DominoTilingsZ.mem_rectangle_iff]
  constructor
  · rintro ⟨dz, ⟨d, hd, rfl⟩, hxy⟩
    rw [toDominoZ_cells] at hxy
    simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff] at hxy
    have hcells := T.dominos_in_rect d hd
    rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hc1 : d.cell1 ∈ DominoTilings.Rectangle n m := by
        apply hcells
        simp [DominoTilings.Domino.cells]
      rw [DominoTilings.mem_Rectangle] at hc1
      constructor <;> omega
    · have hc2 : d.cell2 ∈ DominoTilings.Rectangle n m := by
        apply hcells
        simp [DominoTilings.Domino.cells]
      rw [DominoTilings.mem_Rectangle] at hc2
      constructor <;> omega
  · intro ⟨hx1, hx2, hy1, hy2⟩
    -- The cell (x, y) is in the ℕ rectangle
    have hmem : (x.toNat, y.toNat) ∈ DominoTilings.Rectangle n m := by
      rw [DominoTilings.mem_Rectangle]
      constructor <;> omega
    -- So it's covered by some domino in T
    have hcover := T.covers_all
    rw [Finset.ext_iff] at hcover
    have := (hcover (x.toNat, y.toNat)).mpr hmem
    simp only [Finset.mem_biUnion] at this
    obtain ⟨d, hd, hcell⟩ := this
    refine ⟨toDominoZ d, ⟨d, hd, rfl⟩, ?_⟩
    rw [toDominoZ_cells]
    simp only [cellsZ, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    simp only [DominoTilings.Domino.cells] at hcell
    simp at hcell
    rcases hcell with hc1 | hc2
    · left
      have h1 : x.toNat = d.cell1.1 := congrArg Prod.fst hc1
      have h2 : y.toNat = d.cell1.2 := congrArg Prod.snd hc1
      constructor <;> omega
    · right
      have h1 : x.toNat = d.cell2.1 := congrArg Prod.fst hc2
      have h2 : y.toNat = d.cell2.2 := congrArg Prod.snd hc2
      constructor <;> omega

end TilingEquivalence
end DominoBridge
