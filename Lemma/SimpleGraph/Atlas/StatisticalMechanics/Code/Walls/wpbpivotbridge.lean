import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wpbpivotbridge.Part3
open Finset SimpleGraph Function StatMech StatMech.Wpb


/--
[wpb_pivot_inj_nonpinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_pivot_inj_nonpinch_eq
  {K : Set (Site 2)}
  {e e' : Dart}
-- given
  (he : IsBoundaryDart K e)
  (he' : IsBoundaryDart K e')
  (hnp : ¬(wcd_frontCell e ∈ K ∧ wcd_sideCell e ∉ K))
  (hpv : wcd_pivot e = wcd_pivot e') :
-- imply
  e = e' := by
-- proof
  apply StatMech.Wpb.wpb_pivot_inj_nonpinch K he he' hnp hpv

/--
[wpb_pivotInjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_pivotInjective_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hpf : WpbPinchFree K a) :
-- imply
  Set.InjOn (fun i => wcd_pivot ((dartNext K)^[i] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Wpb.wpb_pivotInjective K a hpf

/--
[wpb_unitWt_e1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_unitWt_e1_eq :
-- imply
  unitWt (![1, 0] : Site 2) = 1 := by
-- proof
  apply StatMech.Wpb.wpb_unitWt_e1

/--
[wpb_unitWt_me1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_unitWt_me1_eq :
-- imply
  unitWt (![-1, 0] : Site 2) = 1 := by
-- proof
  apply StatMech.Wpb.wpb_unitWt_me1

/--
[wpb_unitWt_e2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_unitWt_e2_eq :
-- imply
  unitWt (![0, 1] : Site 2) = 1 := by
-- proof
  apply StatMech.Wpb.wpb_unitWt_e2

/--
[wpb_unitWt_me2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_unitWt_me2_eq :
-- imply
  unitWt (![0, -1] : Site 2) = 1 := by
-- proof
  apply StatMech.Wpb.wpb_unitWt_me2

/--
[wpb_defect_zero_of_no_boundary_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_defect_zero_of_no_boundary_pivot_eq
  {K : Set (Site 2)}
  {x y : ℤ}
-- given
  (hK : K.Finite)
  (hv : ((x, y) : ℤ × ℤ) ∈ regVerts (wcd_toVtxFinset K hK))
  (hnp : ∀ e : Dart, IsBoundaryDart K e → wcd_pivot e ≠ (x, y)) :
-- imply
  defect (wcd_toVtxFinset K hK) (x, y) = 0 := by
-- proof
  apply StatMech.Wpb.wpb_defect_zero_of_no_boundary_pivot K hK x y hv hnp

/--
[wpb_covering_of_orbitCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_covering_of_orbitCovers_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hcov : WpbOrbitCovers K a) :
-- imply
  ∀ v ∈ regVerts (wcd_toVtxFinset K hK), v ∉ (Finset.range (dartOrbitPeriod K a)).image (fun i => wcd_pivot ((dartNext K)^[i] a.1)) → defect (wcd_toVtxFinset K hK) v = 0 := by
-- proof
  apply StatMech.Wpb.wpb_covering_of_orbitCovers K hK a hcov

/--
[wpb_pivotBridge_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_pivotBridge_of_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hcov : WpbOrbitCovers K a) :
-- imply
  WcdPivotBridge K hK a := by
-- proof
  apply StatMech.Wpb.wpb_pivotBridge_of K hK a hpf hcov

/--
[wpb_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hcov : WpbOrbitCovers K a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Wpb.wpb_revCount_pm_one K hK a hpf hcov hbuild

/--
[wpb_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hK : K.Finite)
  (hpf : WpbPinchFree K a)
  (hcov : WpbOrbitCovers K a)
  (hbuild : EucBuildable (wcd_toVtxFinset K hK)) :
-- imply
  BalanceIsFour K a := by
-- proof
  apply StatMech.Wpb.wpb_balanceIsFour K hK a hpf hcov hbuild

/--
[wpb_frontCell_notMem_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_frontCell_notMem_unitCell_eq
  {e : Dart}
-- given
  (he : IsBoundaryDart unitCell e) :
-- imply
  wcd_frontCell e ∉ unitCell := by
-- proof
  apply StatMech.Wpb.wpb_frontCell_notMem_unitCell e he

/--
[wpb_witness_pinchFree_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_witness_pinchFree_unitCell_eq :
-- imply
  WpbPinchFree unitCell ucBase := by
-- proof
  apply StatMech.Wpb.wpb_witness_pinchFree_unitCell

/--
[wpb_witness_orbitCovers_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_witness_orbitCovers_unitCell_eq :
-- imply
  WpbOrbitCovers unitCell ucBase := by
-- proof
  apply StatMech.Wpb.wpb_witness_orbitCovers_unitCell

/--
[wpb_witness_pivotBridge_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_witness_pivotBridge_unitCell_eq :
-- imply
  WcdPivotBridge unitCell wcd_unitCell_finite ucBase := by
-- proof
  apply StatMech.Wpb.wpb_witness_pivotBridge_unitCell

/--
[wpb_witness_revCount_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean)
-/
@[path]
private lemma wpb_witness_revCount_unitCell_eq :
-- imply
  revCount unitCell ucBase = -1 := by
-- proof
  apply StatMech.Wpb.wpb_witness_revCount_unitCell


-- created on 2026-10-23
