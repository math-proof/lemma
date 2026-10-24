import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneP2CoordinateToggleObstruction


/--
[actualMass_active_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateToggleObstruction.lean)
-/
@[path]
private lemma actualMass_active_of_data_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {R : CoordinateToggleData S beta J d s ss hs}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateToggleObstruction.actualMass_active_of_data S beta J d s ss hs R

/--
[coordinateToggleData_isEmpty_of_left_zero_right_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateToggleObstruction.lean)
-/
@[path]
private lemma coordinateToggleData_isEmpty_of_left_zero_right_ne_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (hleft : S.actualMass beta J d (s :: ss) = 0)
  (hright : shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss ≠ 0) :
-- imply
  IsEmpty (CoordinateToggleData S beta J d s ss hs) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateToggleObstruction.coordinateToggleData_isEmpty_of_left_zero_right_ne S beta J d s ss hs hleft hright

/--
[vacuumActualMass_cons_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateToggleObstruction.lean)
-/
@[path]
private lemma vacuumActualMass_cons_eq_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (J : Sym2 V -> Real) :
-- imply
  shb_vacuumPartialSelector.actualMass beta J d (s :: ss) = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateToggleObstruction.vacuumActualMass_cons_eq_zero beta J d s ss

/--
[vacuumCoordinateToggleData_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateToggleObstruction.lean)
-/
@[path]
private lemma vacuumCoordinateToggleData_isEmpty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (hsegment : shb_segmentNum beta J d s ≠ 0) :
-- imply
  IsEmpty (CoordinateToggleData shb_vacuumPartialSelector beta J d s [] hs) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateToggleObstruction.vacuumCoordinateToggleData_isEmpty beta J d s hs hsegment


-- created on 2026-10-23
