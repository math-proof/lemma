import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc2_thickshelf
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc2_downCell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_downCell_eq_eq
  {v : Site 2} :
-- imply
  jc2_downCell v = v + ![0, -1] := by
-- proof
  apply StatMech.Walls.jc2_downCell_eq v

/--
[jc2_downCell_run](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_downCell_run_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  jc2_downCell (c + ![j, 0]) = c + ![j, -1] := by
-- proof
  apply StatMech.Walls.jc2_downCell_run c j

/--
[jc2_shelfCell_coord1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelfCell_coord1_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  (c + ![j, -1] : Site 2) 1 = c 1 - 1 := by
-- proof
  apply StatMech.Walls.jc2_shelfCell_coord1 c j

/--
[jc2_shelfCell_coord0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelfCell_coord0_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  (c + ![j, -1] : Site 2) 0 = c 0 + j := by
-- proof
  apply StatMech.Walls.jc2_shelfCell_coord0 c j

/--
[jc2_shelf_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelf_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len) :
-- imply
  ∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.jc2_shelf_mem K c len hthick

/--
[jc2_shelf_adj_run](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelf_adj_run_eq
  {c : Site 2}
  {j : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1]) := by
-- proof
  apply StatMech.Walls.jc2_shelf_adj_run c j

/--
[jc2_shelf_below_topRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelf_below_topRow_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {j : ℤ}
-- given
  (_hrun : jc_IsTopRowRun K c len) :
-- imply
  (c + ![j, -1] : Site 2) 1 < c 1 := by
-- proof
  apply StatMech.Walls.jc2_shelf_below_topRow K c len _hrun j

/--
[jc2_shelf_left_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelf_left_end_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  (c + ![0, -1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.jc2_shelf_left_end K c len hthick hlen

/--
[jc2_shelf_right_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_shelf_right_end_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  (c + ![len, -1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.jc2_shelf_right_end K c len hthick hlen

/--
[jc2_thickShelf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_thickShelf_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hthick : jc2_FullyThick K c len) :
-- imply
  (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K) ∧ (∀ j : ℤ, (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1])) ∧ (∀ j : ℤ, (c + ![j, -1] : Site 2) 1 < c 1) := by
-- proof
  apply StatMech.Walls.jc2_thickShelf K c len hrun hthick

/--
[jc2_thickShelf_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_thickShelf_explicit_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hthick : jc2_FullyThick K c len)
  (hlen : 0 ≤ len) :
-- imply
  (∀ j : ℤ, 0 ≤ j → j ≤ len → (c + ![j, -1] : Site 2) ∈ K) ∧ (∀ j : ℤ, (hypercubicLattice 2).Adj (c + ![j, 0]) (c + ![j, -1])) ∧ (∀ j : ℤ, (c + ![j, -1] : Site 2) 1 < c 1) ∧ (c + ![0, -1] : Site 2) ∈ K ∧ (c + ![len, -1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Walls.jc2_thickShelf_explicit K c len hrun hthick hlen

/--
[jc2_domino_not_fullyThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_domino_not_fullyThick_eq :
-- imply
  ¬ jc2_FullyThick domino (![0, 0] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc2_domino_not_fullyThick

/--
[jc2_block2_fullyThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_block2_fullyThick_eq :
-- imply
  jc2_FullyThick jc2_block2 (![0, 1] : Site 2) 1 := by
-- proof
  apply StatMech.Walls.jc2_block2_fullyThick

/--
[jc2_block2_shelf_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc2_thickshelf.lean)
-/
@[path]
private lemma jc2_block2_shelf_mem_eq :
-- imply
  ∀ j : ℤ, 0 ≤ j → j ≤ 1 → ((![0, 1] : Site 2) + ![j, -1]) ∈ jc2_block2 := by
-- proof
  apply StatMech.Walls.jc2_block2_shelf_mem


-- created on 2026-10-23
