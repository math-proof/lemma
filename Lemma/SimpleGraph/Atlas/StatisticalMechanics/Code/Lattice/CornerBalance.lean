import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.CornerBalance
open SimpleGraph Function StatMech StatMech.Lattice


/--
[totalTurnZ_eq_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma totalTurnZ_eq_cornerBalance_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  totalTurnZ K e p = rightCornerCount K e p - leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.totalTurnZ_eq_cornerBalance K e p

/--
[turningIsFullRevolution_of_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_cornerBalance_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨ rightCornerCount K a.1 (dartOrbitPeriod K a) - leftCornerCount K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_cornerBalance K a h

/--
[totalTurnZ_four_of_all_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma totalTurnZ_four_of_all_left_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : turnZ K e = -1)
  (h1 : turnZ K (dartNext K e) = -1)
  (h2 : turnZ K ((dartNext K)^[2] e) = -1)
  (h3 : turnZ K ((dartNext K)^[3] e) = -1) :
-- imply
  totalTurnZ K e 4 = -4 := by
-- proof
  apply StatMech.Lattice.totalTurnZ_four_of_all_left K e h0 h1 h2 h3

/--
[unitCell_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitCell_finite_eq :
-- imply
  unitCell.Finite := by
-- proof
  apply StatMech.Lattice.unitCell_finite

/--
[origin_mem_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma origin_mem_unitCell_eq :
-- imply
  (![0, 0] : Site 2) ∈ unitCell := by
-- proof
  apply StatMech.Lattice.origin_mem_unitCell

/--
[not_mem_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma not_mem_unitCell_eq
  {v : Site 2}
-- given
  (h : v 0 ≠ 0 ∨ v 1 ≠ 0) :
-- imply
  v ∉ unitCell := by
-- proof
  apply StatMech.Lattice.not_mem_unitCell v h

/--
[unitWt_px](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitWt_px_eq :
-- imply
  unitWt (![1, 0] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_px

/--
[unitWt_my](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitWt_my_eq :
-- imply
  unitWt (![0, -1] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_my

/--
[unitWt_mx](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitWt_mx_eq :
-- imply
  unitWt (![-1, 0] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_mx

/--
[unitWt_py](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitWt_py_eq :
-- imply
  unitWt (![0, 1] : Site 2) = 1 := by
-- proof
  apply StatMech.Lattice.unitWt_py

/--
[ucDart0_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_tail_eq :
-- imply
  ucDart0.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.ucDart0_tail

/--
[ucDart1_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_tail_eq :
-- imply
  ucDart1.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.ucDart1_tail

/--
[ucDart2_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_tail_eq :
-- imply
  ucDart2.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.ucDart2_tail

/--
[ucDart3_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_tail_eq :
-- imply
  ucDart3.tail = ![0, 0] := by
-- proof
  apply StatMech.Lattice.ucDart3_tail

/--
[ucDart0_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_dir_eq :
-- imply
  ucDart0.dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart0_dir

/--
[ucDart1_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_dir_eq :
-- imply
  ucDart1.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.ucDart1_dir

/--
[ucDart2_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_dir_eq :
-- imply
  ucDart2.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart2_dir

/--
[ucDart3_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_dir_eq :
-- imply
  ucDart3.dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.ucDart3_dir

/--
[ucDart0_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_head_eq :
-- imply
  ucDart0.head = ![1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart0_head

/--
[ucDart1_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_head_eq :
-- imply
  ucDart1.head = ![0, -1] := by
-- proof
  apply StatMech.Lattice.ucDart1_head

/--
[ucDart2_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_head_eq :
-- imply
  ucDart2.head = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart2_head

/--
[ucDart3_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_head_eq :
-- imply
  ucDart3.head = ![0, 1] := by
-- proof
  apply StatMech.Lattice.ucDart3_head

/--
[ucDart0_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_boundary_eq :
-- imply
  IsBoundaryDart unitCell ucDart0 := by
-- proof
  apply StatMech.Lattice.ucDart0_boundary

/--
[ucDart1_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_boundary_eq :
-- imply
  IsBoundaryDart unitCell ucDart1 := by
-- proof
  apply StatMech.Lattice.ucDart1_boundary

/--
[ucDart2_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_boundary_eq :
-- imply
  IsBoundaryDart unitCell ucDart2 := by
-- proof
  apply StatMech.Lattice.ucDart2_boundary

/--
[ucDart3_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_boundary_eq :
-- imply
  IsBoundaryDart unitCell ucDart3 := by
-- proof
  apply StatMech.Lattice.ucDart3_boundary

/--
[ucDart0_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_travel_eq :
-- imply
  -rot90Fun ucDart0.dir = ![0, -1] := by
-- proof
  apply StatMech.Lattice.ucDart0_travel

/--
[ucDart1_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_travel_eq :
-- imply
  -rot90Fun ucDart1.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart1_travel

/--
[ucDart2_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_travel_eq :
-- imply
  -rot90Fun ucDart2.dir = ![0, 1] := by
-- proof
  apply StatMech.Lattice.ucDart2_travel

/--
[ucDart3_travel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_travel_eq :
-- imply
  -rot90Fun ucDart3.dir = ![1, 0] := by
-- proof
  apply StatMech.Lattice.ucDart3_travel

/--
[ucDart0_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_front_nmem_eq :
-- imply
  ucDart0.head + (-rot90Fun ucDart0.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart0_front_nmem

/--
[ucDart0_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_side_nmem_eq :
-- imply
  ucDart0.tail + (-rot90Fun ucDart0.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart0_side_nmem

/--
[ucDart1_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_front_nmem_eq :
-- imply
  ucDart1.head + (-rot90Fun ucDart1.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart1_front_nmem

/--
[ucDart1_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_side_nmem_eq :
-- imply
  ucDart1.tail + (-rot90Fun ucDart1.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart1_side_nmem

/--
[ucDart2_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_front_nmem_eq :
-- imply
  ucDart2.head + (-rot90Fun ucDart2.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart2_front_nmem

/--
[ucDart2_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_side_nmem_eq :
-- imply
  ucDart2.tail + (-rot90Fun ucDart2.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart2_side_nmem

/--
[ucDart3_front_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_front_nmem_eq :
-- imply
  ucDart3.head + (-rot90Fun ucDart3.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart3_front_nmem

/--
[ucDart3_side_nmem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_side_nmem_eq :
-- imply
  ucDart3.tail + (-rot90Fun ucDart3.dir) ∉ unitCell := by
-- proof
  apply StatMech.Lattice.ucDart3_side_nmem

/--
[ucDart0_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart0_turnZ_eq :
-- imply
  turnZ unitCell ucDart0 = -1 := by
-- proof
  apply StatMech.Lattice.ucDart0_turnZ

/--
[ucDart1_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart1_turnZ_eq :
-- imply
  turnZ unitCell ucDart1 = -1 := by
-- proof
  apply StatMech.Lattice.ucDart1_turnZ

/--
[ucDart2_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart2_turnZ_eq :
-- imply
  turnZ unitCell ucDart2 = -1 := by
-- proof
  apply StatMech.Lattice.ucDart2_turnZ

/--
[ucDart3_turnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucDart3_turnZ_eq :
-- imply
  turnZ unitCell ucDart3 = -1 := by
-- proof
  apply StatMech.Lattice.ucDart3_turnZ

/--
[dartNext_ucDart0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma dartNext_ucDart0_eq :
-- imply
  dartNext unitCell ucDart0 = ucDart1 := by
-- proof
  apply StatMech.Lattice.dartNext_ucDart0

/--
[dartNext_ucDart1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma dartNext_ucDart1_eq :
-- imply
  dartNext unitCell ucDart1 = ucDart2 := by
-- proof
  apply StatMech.Lattice.dartNext_ucDart1

/--
[dartNext_ucDart2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma dartNext_ucDart2_eq :
-- imply
  dartNext unitCell ucDart2 = ucDart3 := by
-- proof
  apply StatMech.Lattice.dartNext_ucDart2

/--
[dartNext_ucDart3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma dartNext_ucDart3_eq :
-- imply
  dartNext unitCell ucDart3 = ucDart0 := by
-- proof
  apply StatMech.Lattice.dartNext_ucDart3

/--
[iterate_ucDart_1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma iterate_ucDart_1_eq :
-- imply
  (dartNext unitCell)^[1] ucDart0 = ucDart1 := by
-- proof
  apply StatMech.Lattice.iterate_ucDart_1

/--
[iterate_ucDart_2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma iterate_ucDart_2_eq :
-- imply
  (dartNext unitCell)^[2] ucDart0 = ucDart2 := by
-- proof
  apply StatMech.Lattice.iterate_ucDart_2

/--
[iterate_ucDart_3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma iterate_ucDart_3_eq :
-- imply
  (dartNext unitCell)^[3] ucDart0 = ucDart3 := by
-- proof
  apply StatMech.Lattice.iterate_ucDart_3

/--
[iterate_ucDart_4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma iterate_ucDart_4_eq :
-- imply
  (dartNext unitCell)^[4] ucDart0 = ucDart0 := by
-- proof
  apply StatMech.Lattice.iterate_ucDart_4

/--
[unitCell_totalTurnZ_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitCell_totalTurnZ_four_eq :
-- imply
  totalTurnZ unitCell ucDart0 4 = -4 := by
-- proof
  apply StatMech.Lattice.unitCell_totalTurnZ_four

/--
[ucBase_isPeriodicPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucBase_isPeriodicPt_eq :
-- imply
  Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase := by
-- proof
  apply StatMech.Lattice.ucBase_isPeriodicPt

/--
[ucBase_not_fixedPt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucBase_not_fixedPt_eq :
-- imply
  ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase := by
-- proof
  apply StatMech.Lattice.ucBase_not_fixedPt

/--
[ucBase_not_periodic_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma ucBase_not_periodic_two_eq :
-- imply
  ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase := by
-- proof
  apply StatMech.Lattice.ucBase_not_periodic_two

/--
[unitCell_orbitPeriod_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitCell_orbitPeriod_eq_four_eq :
-- imply
  dartOrbitPeriod unitCell ucBase = 4 := by
-- proof
  apply StatMech.Lattice.unitCell_orbitPeriod_eq_four

/--
[unitCell_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitCell_turningIsFullRevolution_eq :
-- imply
  TurningIsFullRevolution unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_turningIsFullRevolution

/--
[unitCell_orbitPeriod_ge_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CornerBalance.lean)
-/
@[path]
private lemma unitCell_orbitPeriod_ge_four_eq :
-- imply
  4 ≤ dartOrbitPeriod unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_orbitPeriod_ge_four


-- created on 2026-10-23
