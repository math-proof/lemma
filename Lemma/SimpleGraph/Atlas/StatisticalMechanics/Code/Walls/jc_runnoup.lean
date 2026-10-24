import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc_runnoup
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc_run_no_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_run_no_up_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {j : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  (c + ![j, 1]) ∉ K := by
-- proof
  apply StatMech.Walls.jc_run_no_up K c len hrun j

/--
[jc_left_end_left_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_left_end_left_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  (c + ![(-1 : ℤ), 0]) ∉ K := by
-- proof
  apply StatMech.Walls.jc_left_end_left_nmem K c len hrun

/--
[jc_right_end_right_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_right_end_right_nmem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  (c + ![len + 1, 0]) ∉ K := by
-- proof
  apply StatMech.Walls.jc_right_end_right_nmem K c len hrun

/--
[jc_run_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_run_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {j : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len)
  (hj0 : 0 ≤ j)
  (hj1 : j ≤ len) :
-- imply
  (c + ![j, 0]) ∈ K := by
-- proof
  apply StatMech.Walls.jc_run_mem K c len hrun j hj0 hj1

/--
[jc_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_runFrame_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  (∀ j : ℤ, (c + ![j, 1]) ∉ K) ∧ (c + ![(-1 : ℤ), 0]) ∉ K ∧ (c + ![len + 1, 0]) ∉ K := by
-- proof
  apply StatMech.Walls.jc_runFrame K c len hrun

/--
[jc_domino_isExtremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_domino_isExtremeCell_eq :
-- imply
  IsExtremeCell domino (![0, 0] : Site 2) where mem := by
-- proof
  apply StatMech.Walls.jc_domino_isExtremeCell

/--
[jc_domino_isTopRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_domino_isTopRowRun_eq :
-- imply
  jc_IsTopRowRun domino (![0, 0] : Site 2) 1 where isExtreme := by
-- proof
  apply StatMech.Walls.jc_domino_isTopRowRun

/--
[jc_domino_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_domino_runFrame_eq :
-- imply
  (∀ j : ℤ, ((![0, 0] : Site 2) + ![j, 1]) ∉ domino) ∧ ((![0, 0] : Site 2) + ![(-1 : ℤ), 0]) ∉ domino ∧ ((![0, 0] : Site 2) + ![(1 : ℤ) + 1, 0]) ∉ domino := by
-- proof
  apply StatMech.Walls.jc_domino_runFrame

/--
[jc_unitCell_isExtremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_unitCell_isExtremeCell_eq :
-- imply
  IsExtremeCell unitCell (![0, 0] : Site 2) where mem := by
-- proof
  apply StatMech.Walls.jc_unitCell_isExtremeCell

/--
[jc_unitCell_isTopRowRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_unitCell_isTopRowRun_eq :
-- imply
  jc_IsTopRowRun unitCell (![0, 0] : Site 2) 0 where isExtreme := by
-- proof
  apply StatMech.Walls.jc_unitCell_isTopRowRun

/--
[jc_unitCell_runFrame](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_runnoup.lean)
-/
@[path]
private lemma jc_unitCell_runFrame_eq :
-- imply
  (∀ j : ℤ, ((![0, 0] : Site 2) + ![j, 1]) ∉ unitCell) ∧ ((![0, 0] : Site 2) + ![(-1 : ℤ), 0]) ∉ unitCell ∧ ((![0, 0] : Site 2) + ![(0 : ℤ) + 1, 0]) ∉ unitCell := by
-- proof
  apply StatMech.Walls.jc_unitCell_runFrame


-- created on 2026-10-23
