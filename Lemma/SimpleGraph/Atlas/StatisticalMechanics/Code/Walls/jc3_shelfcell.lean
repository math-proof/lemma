import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc3_shelfcell
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc3_runRightEnd_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_runRightEnd_def_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc3_runRightEnd c len = c + ![len, 0] := by
-- proof
  apply StatMech.Walls.jc3_runRightEnd_def c len

/--
[jc3_downCell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_eq_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc3_downCell c len = c + ![len, -1] := by
-- proof
  apply StatMech.Walls.jc3_downCell_eq c len

/--
[jc3_downCell_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_coord1_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (jc3_downCell c len) 1 = c 1 - 1 := by
-- proof
  apply StatMech.Walls.jc3_downCell_coord1 c len

/--
[jc3_runRightEnd_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_runRightEnd_coord1_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (jc3_runRightEnd c len) 1 = c 1 := by
-- proof
  apply StatMech.Walls.jc3_runRightEnd_coord1 c len

/--
[jc3_downCell_ne_runRightEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_ne_runRightEnd_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  jc3_downCell c len ≠ jc3_runRightEnd c len := by
-- proof
  apply StatMech.Walls.jc3_downCell_ne_runRightEnd c len

/--
[jc3_downCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc3_downCell c len ∈ K := by
-- proof
  apply StatMech.Walls.jc3_downCell_mem K c len hthick hlen

/--
[jc3_downCell_mem_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_mem_diff_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} := by
-- proof
  apply StatMech.Walls.jc3_downCell_mem_diff K c len hthick hlen

/--
[jc3_downCell_adj_runRightEnd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_downCell_adj_runRightEnd_eq
  {c : Site 2}
  {len : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) := by
-- proof
  apply StatMech.Walls.jc3_downCell_adj_runRightEnd c len

/--
[jc3_shelfCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_shelfCell_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc3_downCell c len = c + ![len, -1] ∧ jc3_downCell c len ∈ K ∧ jc3_downCell c len ≠ jc3_runRightEnd c len ∧ jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧ (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) := by
-- proof
  apply StatMech.Walls.jc3_shelfCell K c len hthick hlen

/--
[jc3_rerouteTarget_in_clip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_rerouteTarget_in_clip_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  jc3_downCell c len ∈ K \ {jc3_runRightEnd c len} ∧ (hypercubicLattice 2).Adj (jc3_runRightEnd c len) (jc3_downCell c len) := by
-- proof
  apply StatMech.Walls.jc3_rerouteTarget_in_clip K c len hthick hlen

/--
[jc3_block2_downCell_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_block2_downCell_mem_eq :
-- imply
  jc3_downCell (![0, 1] : Site 2) 1 ∈ jc2_block2 := by
-- proof
  apply StatMech.Walls.jc3_block2_downCell_mem

/--
[jc3_block2_downCell_mem_diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_shelfcell.lean)
-/
@[path]
private lemma jc3_block2_downCell_mem_diff_eq :
-- imply
  jc3_downCell (![0, 1] : Site 2) 1 ∈ jc2_block2 \ {jc3_runRightEnd (![0, 1] : Site 2) 1} := by
-- proof
  apply StatMech.Walls.jc3_block2_downCell_mem_diff


-- created on 2026-10-23
