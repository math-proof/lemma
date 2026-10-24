import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoBridge
import sympy.matrices.determinants.DominoTilings
import sympy.series.formal.WeightedSets
import Lemma.Nat.DominoTilings
import Lemma.PowerSeries.WeightedSets
open DominoBridge


section
-- ac-theorems


open Finset BigOperators

namespace DominoBridge


/-- Converting DominoTilings.Domino to DominoTilingsZ.Domino produces positive coordinates 
    when all cells are positive. -/
lemma toDominoZ_hasPositiveCoords (d : DominoTilings.Domino)
    (h1 : d.cell1.1 ≥ 1) (h2 : d.cell1.2 ≥ 1) 
    (h3 : d.cell2.1 ≥ 1) (h4 : d.cell2.2 ≥ 1) : hasPositiveCoords (toDominoZ d) := by
  simp only [toDominoZ]
  split_ifs with hH
  · -- Horizontal case
    simp only [hasPositiveCoords, ge_iff_le]
    constructor
    · have hmin : min d.cell1.1 d.cell2.1 ≥ 1 := by omega
      exact_mod_cast hmin
    · exact_mod_cast h2
  · -- Vertical case
    simp only [hasPositiveCoords, ge_iff_le]
    constructor
    · exact_mod_cast h1
    · have hmin : min d.cell1.2 d.cell2.2 ≥ 1 := by omega
      exact_mod_cast hmin

/-- Converting DominoTilingsZ.Domino to DominoTilings.Domino preserves the set of cells (cast to ℤ). -/
lemma toDominoN_cells (d : DominoTilingsZ.Domino) (hpos : hasPositiveCoords d) : 
    cellsZ (toDominoN d hpos) = d.toShape := by
  match d, hpos with
  | .horizontal i j, ⟨hi, hj⟩ =>
    simp only [toDominoN, cellsZ, DominoTilingsZ.Domino.toShape]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
  | .vertical i j, ⟨hi, hj⟩ =>
    simp only [toDominoN, cellsZ, DominoTilingsZ.Domino.toShape]
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.ext_iff]
    constructor
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega
    · rintro (⟨hp1, hp2⟩ | ⟨hp1, hp2⟩)
      · left; constructor <;> omega
      · right; constructor <;> omega

/-- The cells of a domino in canonical form are the same as the original. -/
lemma toCanonical_cells (d : DominoTilings.Domino) : 
    ({(toCanonical d).cell1, (toCanonical d).cell2} : Set (ℕ × ℕ)) = {d.cell1, d.cell2} := by
  simp only [toCanonical]
  split_ifs <;> simp [swap, Set.pair_comm]

/-- The image of DominoTilings.Rectangle under cellToZ equals DominoTilingsZ.Rectangle 
    as sets of ℤ × ℤ. -/
lemma rectangle_correspondence (n m : ℕ) :
    cellToZ '' (DominoTilings.Rectangle n m : Set (ℕ × ℕ)) = DominoTilingsZ.Rectangle n m := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Finset.mem_coe, DominoTilingsZ.mem_rectangle_iff]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, heq⟩
    simp only [cellToZ, Prod.mk.injEq] at heq
    rw [DominoTilings.mem_Rectangle] at hmem
    constructor <;> omega
  · intro ⟨hx1, hx2, hy1, hy2⟩
    refine ⟨(x.toNat, y.toNat), ?_, ?_⟩
    · rw [DominoTilings.mem_Rectangle]
      constructor <;> omega
    · simp only [cellToZ, Prod.mk.injEq]
      constructor <;> omega


section TilingEquivalence

variable {n m : ℕ}

/-- The dominos in a DominoTiling have positive coordinates (cell coords ≥ 1). -/
lemma DominoTiling_dominos_pos (T : DominoTilings.DominoTiling n m) (d : DominoTilings.Domino)
    (hd : d ∈ T.dominos) : d.cell1.1 ≥ 1 ∧ d.cell1.2 ≥ 1 ∧ d.cell2.1 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
  have h := T.dominos_in_rect d hd
  have hc1 : d.cell1 ∈ DominoTilings.Rectangle n m := by
    apply h
    simp [DominoTilings.Domino.cells]
  have hc2 : d.cell2 ∈ DominoTilings.Rectangle n m := by
    apply h
    simp [DominoTilings.Domino.cells]
  rw [DominoTilings.mem_Rectangle] at hc1 hc2
  exact ⟨hc1.1, hc1.2.2.1, hc2.1, hc2.2.2.1⟩


/-- Dominos in a Tiling of a rectangle have positive coordinates. -/
lemma Tiling_dominos_pos (T : DominoTilingsZ.Tiling (DominoTilingsZ.Rectangle n m))
    (d : DominoTilingsZ.Domino) (hd : d ∈ T.dominos) : hasPositiveCoords d := by
  have hcover := T.cover
  have hsub : d.toShape ⊆ DominoTilingsZ.Rectangle n m := by
    rw [← hcover]
    exact Set.subset_biUnion_of_mem hd
  match d with
  | .horizontal i j =>
    simp only [hasPositiveCoords, ge_iff_le]
    have h1 : (i, j) ∈ DominoTilingsZ.Rectangle n m := by
      apply hsub
      simp [DominoTilingsZ.Domino.toShape]
    rw [DominoTilingsZ.mem_rectangle_iff] at h1
    exact ⟨h1.1, h1.2.2.1⟩
  | .vertical i j =>
    simp only [hasPositiveCoords, ge_iff_le]
    have h1 : (i, j) ∈ DominoTilingsZ.Rectangle n m := by
      apply hsub
      simp [DominoTilingsZ.Domino.toShape]
    rw [DominoTilingsZ.mem_rectangle_iff] at h1
    exact ⟨h1.1, h1.2.2.1⟩

/-- toDominoN is injective on dominos with positive coordinates. -/
lemma toDominoN_injective {d1 d2 : DominoTilingsZ.Domino} 
    (hpos1 : hasPositiveCoords d1) (hpos2 : hasPositiveCoords d2)
    (heq : toDominoN d1 hpos1 = toDominoN d2 hpos2) : d1 = d2 := by
  -- Use that toDominoN preserves cells
  have hcells1 := toDominoN_cells d1 hpos1
  have hcells2 := toDominoN_cells d2 hpos2
  -- From heq, we get cellsZ (toDominoN d1 hpos1) = cellsZ (toDominoN d2 hpos2)
  have hcellsZ : cellsZ (toDominoN d1 hpos1) = cellsZ (toDominoN d2 hpos2) := by rw [heq]
  rw [hcells1, hcells2] at hcellsZ
  -- Now d1.toShape = d2.toShape, so d1 = d2
  exact DominoTilingsZ.Domino.eq_of_toShape_eq hcellsZ

end TilingEquivalence

end DominoBridge
end


/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_toDominoZ_hasPositiveCoords
-- given
  (d : DominoTilings.Domino)
  (h0 : d.cell1.1 ≥ 1)
  (h1 : d.cell1.2 ≥ 1)
  (h2 : d.cell2.1 ≥ 1)
  (h3 : d.cell2.2 ≥ 1) :
-- imply
  hasPositiveCoords (toDominoZ d) := by
-- proof
  apply DominoBridge.toDominoZ_hasPositiveCoords d h0 h1 h2 h3

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma toDominoZ_cells
-- given
  (d : DominoTilings.Domino) :
-- imply
  (toDominoZ d).toShape = cellsZ d := by
-- proof
  apply DominoBridge.toDominoZ_cells

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_toDominoN_cells
-- given
  (d : DominoTilingsZ.Domino)
  (hpos : hasPositiveCoords d) :
-- imply
  cellsZ (toDominoN d hpos) = d.toShape := by
-- proof
  apply DominoBridge.toDominoN_cells d hpos

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_toCanonical_cells
-- given
  (d : DominoTilings.Domino) :
-- imply
  ({(toCanonical d).cell1, (toCanonical d).cell2} : Set (ℕ × ℕ)) = {d.cell1, d.cell2} := by
-- proof
  apply DominoBridge.toCanonical_cells

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_rectangle_correspondence
-- given
  (n m : ℕ) :
-- imply
  cellToZ '' (DominoTilings.Rectangle n m : Set (ℕ × ℕ)) = DominoTilingsZ.Rectangle n m := by
-- proof
  apply DominoBridge.rectangle_correspondence

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_DominoTiling_dominos_pos
-- given
  (T : DominoTilings.DominoTiling n m)
  (d : DominoTilings.Domino)
  (hd : d ∈ T.dominos) :
-- imply
  d.cell1.1 ≥ 1 ∧ d.cell1.2 ≥ 1 ∧ d.cell2.1 ≥ 1 ∧ d.cell2.2 ≥ 1 := by
-- proof
  apply DominoBridge.DominoTiling_dominos_pos T d hd

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma toDominoZ_pairwise_disjoint
-- given
  (T : DominoTilings.DominoTiling n m) :
-- imply
  Set.PairwiseDisjoint (dominoFinsetToSet T.dominos) DominoTilingsZ.Domino.toShape := by
-- proof
  apply DominoBridge.toDominoZ_pairwise_disjoint

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma toDominoZ_cover
-- given
  (T : DominoTilings.DominoTiling n m) :
-- imply
  ⋃ d ∈ dominoFinsetToSet T.dominos, d.toShape = DominoTilingsZ.Rectangle n m := by
-- proof
  apply DominoBridge.toDominoZ_cover

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_Tiling_dominos_pos
-- given
  (T : DominoTilingsZ.Tiling (DominoTilingsZ.Rectangle n m))
  (d : DominoTilingsZ.Domino)
  (hd : d ∈ T.dominos) :
-- imply
  hasPositiveCoords d := by
-- proof
  apply DominoBridge.Tiling_dominos_pos T d hd

/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma pv_toDominoN_injective
-- given
  {d1 d2 : DominoTilingsZ.Domino}
  (hpos1 : hasPositiveCoords d1)
  (hpos2 : hasPositiveCoords d2)
  (heq : toDominoN d1 hpos1 = toDominoN d2 hpos2) :
-- imply
  d1 = d2 := by
-- proof
  apply DominoBridge.toDominoN_injective hpos1 hpos2 heq


-- created on 2026-10-20
