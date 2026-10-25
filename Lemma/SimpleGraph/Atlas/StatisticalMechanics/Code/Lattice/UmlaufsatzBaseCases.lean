import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzBaseCases.Part3
open SimpleGraph Function StatMech StatMech.Lattice


/--
[umBase_turnZ_right_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_turnZ_right_iff_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h : e.head + (-rot90Fun e.dir) ∈ K) :
-- imply
  turnZ K e = 1 ∧ (dartNext K e).dir = rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.umBase_turnZ_right_iff K e h

/--
[umBase_turnZ_left_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_turnZ_left_iff_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∉ K) :
-- imply
  turnZ K e = -1 ∧ (dartNext K e).dir = -rot90Fun e.dir := by
-- proof
  apply StatMech.Lattice.umBase_turnZ_left_iff K e h0 h1

/--
[umBase_turnZ_straight_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_turnZ_straight_iff_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (h0 : e.head + (-rot90Fun e.dir) ∉ K)
  (h1 : e.tail + (-rot90Fun e.dir) ∈ K) :
-- imply
  turnZ K e = 0 ∧ (dartNext K e).dir = e.dir := by
-- proof
  apply StatMech.Lattice.umBase_turnZ_straight_iff K e h0 h1

/--
[umBase_turnZ_determines_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_turnZ_determines_dir_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  (dartNext K e).dir = rotPow (turn K e) e.dir := by
-- proof
  apply StatMech.Lattice.umBase_turnZ_determines_dir K e

/--
[umBase_turnAngle_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_turnAngle_mem_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  turnAngle K e = Real.pi / 2 ∨ turnAngle K e = 0 ∨ turnAngle K e = -(Real.pi / 2) := by
-- proof
  apply StatMech.Lattice.umBase_turnAngle_mem K e

/--
[umBase_abs_turnAngle_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_abs_turnAngle_le_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  |turnAngle K e| ≤ Real.pi / 2 := by
-- proof
  apply StatMech.Lattice.umBase_abs_turnAngle_le K e

/--
[umBase_totalTurnAngle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_totalTurnAngle_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  totalTurnAngle K e p = (totalTurnZ K e p : ℝ) * (Real.pi / 2) := by
-- proof
  apply StatMech.Lattice.umBase_totalTurnAngle_eq K e p

/--
[umBase_square_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_square_turnCount_eq :
-- imply
  totalTurnZ unitCell ucDart0 4 = -4 := by
-- proof
  apply StatMech.Lattice.umBase_square_turnCount

/--
[umBase_square_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_square_turning_eq :
-- imply
  totalTurnAngle unitCell ucDart0 4 = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.umBase_square_turning

/--
[umBase_square_turning_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_square_turning_period_eq :
-- imply
  totalTurnAngle unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.umBase_square_turning_period

/--
[umBase_square_rightCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_square_rightCount_eq :
-- imply
  rightCornerCount unitCell ucDart0 4 = 0 := by
-- proof
  apply StatMech.Lattice.umBase_square_rightCount

/--
[umBase_square_leftCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_square_leftCount_eq :
-- imply
  leftCornerCount unitCell ucDart0 4 = 4 := by
-- proof
  apply StatMech.Lattice.umBase_square_leftCount

/--
[umBase_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_cornerBalance_eq :
-- imply
  leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = 4 := by
-- proof
  apply StatMech.Lattice.umBase_cornerBalance

/--
[umBase_cornerBalance_pm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_cornerBalance_pm_eq :
-- imply
  leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = 4 ∨ leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = -4 := by
-- proof
  apply StatMech.Lattice.umBase_cornerBalance_pm

/--
[umBase_cornerBalance_eq_neg_turnCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_cornerBalance_eq_neg_turnCount_eq :
-- imply
  leftCornerCount unitCell ucDart0 4 - rightCornerCount unitCell ucDart0 4 = -(totalTurnZ unitCell ucDart0 4) := by
-- proof
  apply StatMech.Lattice.umBase_cornerBalance_eq_neg_turnCount

/--
[umBase_domino_rightCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_domino_rightCount_eq :
-- imply
  rightCornerCount domino dmD0 6 = 0 := by
-- proof
  apply StatMech.Lattice.umBase_domino_rightCount

/--
[umBase_domino_leftCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_domino_leftCount_eq :
-- imply
  leftCornerCount domino dmD0 6 = 4 := by
-- proof
  apply StatMech.Lattice.umBase_domino_leftCount

/--
[umBase_domino_cornerBalance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_domino_cornerBalance_eq :
-- imply
  leftCornerCount domino dmD0 6 - rightCornerCount domino dmD0 6 = 4 := by
-- proof
  apply StatMech.Lattice.umBase_domino_cornerBalance

/--
[umBase_domino_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UmlaufsatzBaseCases.lean)
-/
@[path]
private lemma umBase_domino_turning_eq :
-- imply
  totalTurnAngle domino dmD0 6 = -(2 * Real.pi) := by
-- proof
  apply StatMech.Lattice.umBase_domino_turning


-- created on 2026-10-23
