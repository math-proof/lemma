import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jcwcutsetwalk
open Set SimpleGraph StatMech StatMech.Walls


/--
[jcw_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_adj_eq
  {x y x' y' : ℤ}
-- given
  (h : (x - x').natAbs + (y - y').natAbs = 1) :
-- imply
  (hypercubicLattice 2).Adj (![x, y] : Site 2) (![x', y'] : Site 2) := by
-- proof
  apply StatMech.Walls.jcw_adj x y x' y' h

/--
[jcw_bottom_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_bottom_mem_cutSet_eq :
-- imply
  s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.jcw_bottom_mem_cutSet

/--
[jcw_right_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_right_mem_cutSet_eq :
-- imply
  s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.jcw_right_mem_cutSet

/--
[jcw_top_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_top_mem_cutSet_eq :
-- imply
  s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.jcw_top_mem_cutSet

/--
[jcw_left_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_left_mem_cutSet_eq :
-- imply
  s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.jcw_left_mem_cutSet

/--
[jcw_shiftSquare_edges_subset_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_shiftSquare_edges_subset_cutSet_eq :
-- imply
  s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.jcw_shiftSquare_edges_subset_cutSet

/--
[jcw_be_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_be_not_mem_eq :
-- imply
  s((![1, 1] : Site 2), (![2, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.jcw_be_not_mem

/--
[jcw_cf_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_cf_not_mem_eq :
-- imply
  s((![1, 2] : Site 2), (![2, 2] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.jcw_cf_not_mem

/--
[jcw_ef_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_ef_not_mem_eq :
-- imply
  s((![2, 1] : Site 2), (![2, 2] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.jcw_ef_not_mem

/--
[jcw_bc_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_bc_mem_eq :
-- imply
  s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.jcw_bc_mem

/--
[jcw_primalWalkBoundsRegion_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_primalWalkBoundsRegion_false_eq :
-- imply
  ¬ PrimalWalkBoundsRegion := by
-- proof
  apply StatMech.Walls.jcw_primalWalkBoundsRegion_false

/--
[jcw_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jcwcutsetwalk.lean)
-/
@[path]
private lemma jcw_status_eq :
-- imply
  (s((![0, 1] : Site 2), (![1, 1] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![1, 1] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![0, 2] : Site 2), (![1, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace ∧ s((![0, 1] : Site 2), (![0, 2] : Site 2)) ∈ jed_cutSet jcw_shiftFace) ∧ (¬ PrimalWalkBoundsRegion) := by
-- proof
  apply StatMech.Walls.jcw_status


-- created on 2026-10-23
