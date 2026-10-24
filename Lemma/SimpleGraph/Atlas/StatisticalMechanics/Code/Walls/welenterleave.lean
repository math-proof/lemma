import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.welenterleave
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wel_enterLeaveAlt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_enterLeaveAlt_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : ℤ}
  {N : ℕ}
-- given
  (hbase : wis_indSeq z Vc c₀ 0 = 0) :
-- imply
  wnu_Alt (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N) := by
-- proof
  apply StatMech.Lattice.wel_enterLeaveAlt z Vc c₀ N hbase

/--
[wel_enterLeaveHead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_enterLeaveHead_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c₀ : ℤ}
  {N : ℕ}
-- given
  (hbase : wis_indSeq z Vc c₀ 0 = 0)
  (hne : wis_nonzeroDiffs (wis_indSeq z Vc c₀) N ≠ []) :
-- imply
  (wis_nonzeroDiffs (wis_indSeq z Vc c₀) N).headI = 1 := by
-- proof
  apply StatMech.Lattice.wel_enterLeaveHead z Vc c₀ N hbase hne

/--
[wel_signsAlternate_of_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_signsAlternate_of_orientationConsistent_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wel_OrientationConsistent z Vc) :
-- imply
  wos_SignsAlternateInColumnOrder z Vc := by
-- proof
  apply StatMech.Lattice.wel_signsAlternate_of_orientationConsistent z Vc h

/--
[wel_signEqIndicatorJumps_of_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_signEqIndicatorJumps_of_orientationConsistent_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wel_OrientationConsistent z Vc) :
-- imply
  wis_SignEqIndicatorJumps z Vc := by
-- proof
  apply StatMech.Lattice.wel_signEqIndicatorJumps_of_orientationConsistent z Vc h

/--
[wel_columnAlternates_of_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_columnAlternates_of_orientationConsistent_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wel_OrientationConsistent z Vc) :
-- imply
  wna_ColumnAlternates z Vc := by
-- proof
  apply StatMech.Lattice.wel_columnAlternates_of_orientationConsistent z Vc h

/--
[wel_signedCross_abs_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_signedCross_abs_le_one_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wel_OrientationConsistent z Vc) :
-- imply
  |wnd_signedCross z Vc| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wel_signedCross_abs_le_one z Vc h

/--
[wel_signedCross_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_signedCross_pm_one_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wel_OrientationConsistent z Vc)
  (hodd : ¬ Even (jec_rayCount z Vc)) :
-- imply
  wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 := by
-- proof
  apply StatMech.Lattice.wel_signedCross_pm_one z Vc h hodd

/--
[wel_doubleSquare_list_not_alternates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_doubleSquare_list_not_alternates_eq :
-- imply
  ¬ wnu_Alt ([1, 1] : List ℤ) := by
-- proof
  apply StatMech.Lattice.wel_doubleSquare_list_not_alternates

/--
[wel_doubleSquare_not_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_doubleSquare_not_orientationConsistent_eq :
-- imply
  ¬ wel_OrientationConsistent (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wel_doubleSquare_not_orientationConsistent

/--
[wel_twoToggle_bothBranches_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_twoToggle_bothBranches_alternate_eq :
-- imply
  wnu_Alt ([1, -1] : List ℤ) ∧ wnu_Alt (([1, -1] : List ℤ).map (fun x => -x)) := by
-- proof
  apply StatMech.Lattice.wel_twoToggle_bothBranches_alternate

/--
[wel_unitSquare_signsAlternate_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/welenterleave.lean)
-/
@[path]
private lemma wel_unitSquare_signsAlternate_consistent_eq :
-- imply
  wos_SignsAlternateInColumnOrder (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wel_unitSquare_signsAlternate_consistent


-- created on 2026-10-23
