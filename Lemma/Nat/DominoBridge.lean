import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoBridge
import sympy.matrices.determinants.DominoTilings
import sympy.series.formal.WeightedSets
open DominoBridge


/--
[DominoBridge](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoBridge.lean)
-/
@[path]
private lemma toDominoZ_hasPositiveCoords
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
private lemma toDominoN_cells
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
private lemma toCanonical_cells
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
private lemma rectangle_correspondence
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
private lemma DominoTiling_dominos_pos
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
private lemma Tiling_dominos_pos
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
private lemma toDominoN_injective
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
