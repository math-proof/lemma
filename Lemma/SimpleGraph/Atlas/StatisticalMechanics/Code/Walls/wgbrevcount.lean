import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wgbrevcount.Part2
open SimpleGraph Function StatMech StatMech.Lattice


/--
[wgb_revCount_iff_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_revCount_iff_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Lattice.wgb_revCount_iff_eulerCharOne K a hp

/--
[wgb_revCount_pm_one_iff_windsBoth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_revCount_pm_one_iff_windsBoth_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (revCount K a = 1 ∨ revCount K a = -1) ↔ (wgb_WindsAtMostOnce K a ∧ wgb_WindsAtLeastOnce K a) := by
-- proof
  apply StatMech.Lattice.wgb_revCount_pm_one_iff_windsBoth K a

/--
[wgb_windsAtMostOnce_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_windsAtMostOnce_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  wgb_WindsAtMostOnce K a ↔ |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ 4 := by
-- proof
  apply StatMech.Lattice.wgb_windsAtMostOnce_iff K a

/--
[wgb_windsAtLeastOnce_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_windsAtLeastOnce_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  wgb_WindsAtLeastOnce K a ↔ totalTurnZ K a.1 (dartOrbitPeriod K a) ≠ 0 := by
-- proof
  apply StatMech.Lattice.wgb_windsAtLeastOnce_iff K a

/--
[wgb_revCount_abs_le_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_revCount_abs_le_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  |revCount K a| ≤ (dartOrbitPeriod K a : ℤ) := by
-- proof
  apply StatMech.Lattice.wgb_revCount_abs_le_period K a

/--
[wgb_turningBound_weaker_than_windsAtMostOnce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_turningBound_weaker_than_windsAtMostOnce_eq :
-- imply
  ∃ (p : ℕ) (r : ℤ), 4 ≤ p ∧ |r| ≤ (p : ℤ) ∧ ¬ (|r| ≤ 1) := by
-- proof
  apply StatMech.Lattice.wgb_turningBound_weaker_than_windsAtMostOnce

/--
[wgb_contourEulerChar_carries_no_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_contourEulerChar_carries_no_winding_eq
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  contourEulerChar p = 1 := by
-- proof
  apply StatMech.Lattice.wgb_contourEulerChar_carries_no_winding hp

/--
[wgb_eulerCharOne_is_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_eulerCharOne_is_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Lattice.wgb_eulerCharOne_is_revCount_pm_one K a hp

/--
[wgb_regChi_holeyRing_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_regChi_holeyRing_ne_one_eq :
-- imply
  StatMech.Euc.regChi ({((0:ℤ),(0:ℤ)),(1,0),(2,0),(0,1),(2,1),(0,2),(1,2),(2,2)} : Finset StatMech.Euc.Cell) ≠ 1 := by
-- proof
  apply StatMech.Lattice.wgb_regChi_holeyRing_ne_one

/--
[wgb_regChi_eq_one_of_buildable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_regChi_eq_one_of_buildable_eq
  {K : Finset StatMech.Euc.Cell}
-- given
  (hK : StatMech.Euc.EucBuildable K) :
-- imply
  StatMech.Euc.regChi K = 1 := by
-- proof
  apply StatMech.Lattice.wgb_regChi_eq_one_of_buildable hK

/--
[wgb_revCount_pm_one_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_revCount_pm_one_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.wgb_revCount_pm_one_of_eulerCharOne K a hp h

/--
[wgb_unitCell_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_unitCell_revCount_pm_one_eq :
-- imply
  revCount unitCell ucBase = 1 ∨ revCount unitCell ucBase = -1 := by
-- proof
  apply StatMech.Lattice.wgb_unitCell_revCount_pm_one

/--
[wgb_domino_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wgbrevcount.lean)
-/
@[path]
private lemma wgb_domino_revCount_pm_one_eq :
-- imply
  revCount domino dmBase = 1 ∨ revCount domino dmBase = -1 := by
-- proof
  apply StatMech.Lattice.wgb_domino_revCount_pm_one


-- created on 2026-10-23
