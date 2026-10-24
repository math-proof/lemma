import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.umffullrev
open SimpleGraph Function StatMech StatMech.Lattice


/--
[umf_totalTurn_eq_four_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_totalTurn_eq_four_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmax : umf_WindsAtMostOnce K a)
  (hmin : umf_WindsAtLeastOnce K a) :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 ∨ totalTurnZ K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.umf_totalTurn_eq_four_of_winds K a hmax hmin

/--
[umf_turningIsFullRevolution_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_turningIsFullRevolution_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hmax : umf_WindsAtMostOnce K a)
  (hmin : umf_WindsAtLeastOnce K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.umf_turningIsFullRevolution_of_winds K a hmax hmin

/--
[umf_winds_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_winds_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a := by
-- proof
  apply StatMech.Lattice.umf_winds_of_fullRevolution K a h

/--
[umf_winds_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_winds_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a) ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.umf_winds_iff K a

/--
[umf_eulerCharOne_iff_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_eulerCharOne_iff_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ (umf_WindsAtMostOnce K a ∧ umf_WindsAtLeastOnce K a) := by
-- proof
  apply StatMech.Lattice.umf_eulerCharOne_iff_winds K a hp

/--
[umf_eulerCharOne_iff_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_eulerCharOne_iff_turningIsFullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.umf_eulerCharOne_iff_turningIsFullRevolution K a hp

/--
[umf_fullRevolution_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_fullRevolution_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.umf_fullRevolution_of_eulerCharOne K a hp h

/--
[umf_revCount_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_revCount_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.umf_revCount_of_eulerCharOne K a hp h

/--
[umf_eulerCharOne_of_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_eulerCharOne_of_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : revCount K a = 1 ∨ revCount K a = -1) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.umf_eulerCharOne_of_revCount_pm_one K a hp h

/--
[umf_convex_minus_reflex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_convex_minus_reflex_eq_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  leftCornerCount K e p - rightCornerCount K e p = - totalTurnZ K e p := by
-- proof
  apply StatMech.Lattice.umf_convex_minus_reflex_eq K e p

/--
[umf_leftCornerCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_leftCornerCount_nonneg_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  0 ≤ leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.umf_leftCornerCount_nonneg K e p

/--
[umf_rightCornerCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_rightCornerCount_nonneg_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  0 ≤ rightCornerCount K e p := by
-- proof
  apply StatMech.Lattice.umf_rightCornerCount_nonneg K e p

/--
[umf_four_convex_of_totalTurn_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_four_convex_of_totalTurn_neg_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.umf_four_convex_of_totalTurn_neg K a h

/--
[umf_four_reflex_of_totalTurn_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_four_reflex_of_totalTurn_pos_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4) :
-- imply
  4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.umf_four_reflex_of_totalTurn_pos K a h

/--
[umf_four_corners_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_four_corners_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨ 4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.umf_four_corners_of_fullRevolution K a h

/--
[umf_four_convex_or_reflex_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_four_convex_or_reflex_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨ 4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.umf_four_convex_or_reflex_of_eulerCharOne K a hp h

/--
[umf_four_convex_of_eulerCharOne_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_four_convex_of_eulerCharOne_neg_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (_hp : 3 ≤ dartOrbitPeriod K a)
  (_h : EulerCharOne K a)
  (hor : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.umf_four_convex_of_eulerCharOne_neg K a _hp _h hor

/--
[umf_unitCell_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_fullRevolution_eq :
-- imply
  TurningIsFullRevolution unitCell ucBase := by
-- proof
  apply StatMech.Lattice.umf_unitCell_fullRevolution

/--
[umf_unitCell_totalTurn_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_totalTurn_neg_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.umf_unitCell_totalTurn_neg

/--
[umf_unitCell_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_eulerCharOne_eq :
-- imply
  EulerCharOne unitCell ucBase := by
-- proof
  apply StatMech.Lattice.umf_unitCell_eulerCharOne

/--
[umf_unitCell_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_revCount_eq :
-- imply
  revCount unitCell ucBase = -1 := by
-- proof
  apply StatMech.Lattice.umf_unitCell_revCount

/--
[umf_unitCell_four_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_four_convex_eq :
-- imply
  4 ≤ leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.umf_unitCell_four_convex

/--
[umf_unitCell_convex_minus_reflex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_unitCell_convex_minus_reflex_eq :
-- imply
  leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) - rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 := by
-- proof
  apply StatMech.Lattice.umf_unitCell_convex_minus_reflex

/--
[umf_Ltromino_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_Ltromino_kingSaturated_eq :
-- imply
  npm_KingSaturated umf_Ltromino := by
-- proof
  apply StatMech.Lattice.umf_Ltromino_kingSaturated

/--
[umf_Ltromino_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umffullrev.lean)
-/
@[path]
private lemma umf_Ltromino_faceMultiplicityOne_eq
  {a : {e : Dart // IsBoundaryDart umf_Ltromino e}} :
-- imply
  usc_FaceMultiplicityOne umf_Ltromino a := by
-- proof
  apply StatMech.Lattice.umf_Ltromino_faceMultiplicityOne a


-- created on 2026-10-23
