import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.umlturning
open SimpleGraph Function StatMech StatMech.Lattice


/--
[uml_four_dvd_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_four_dvd_totalTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uml_four_dvd_totalTurn K a

/--
[uml_cornerBalance_eq_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_cornerBalance_eq_totalTurn_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  leftCornerCount K e p - rightCornerCount K e p = - totalTurnZ K e p := by
-- proof
  apply StatMech.Lattice.uml_cornerBalance_eq_totalTurn K e p

/--
[uml_leftCornerCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_leftCornerCount_nonneg_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  0 ≤ leftCornerCount K e p := by
-- proof
  apply StatMech.Lattice.uml_leftCornerCount_nonneg K e p

/--
[uml_rightCornerCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_rightCornerCount_nonneg_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  0 ≤ rightCornerCount K e p := by
-- proof
  apply StatMech.Lattice.uml_rightCornerCount_nonneg K e p

/--
[uml_four_convex_minus_reflex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_four_convex_minus_reflex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  leftCornerCount K a.1 (dartOrbitPeriod K a) - rightCornerCount K a.1 (dartOrbitPeriod K a) = 4 ∨ leftCornerCount K a.1 (dartOrbitPeriod K a) - rightCornerCount K a.1 (dartOrbitPeriod K a) = -4 := by
-- proof
  apply StatMech.Lattice.uml_four_convex_minus_reflex K a h

/--
[uml_four_convex_of_totalTurn_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_four_convex_of_totalTurn_neg_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = -4) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uml_four_convex_of_totalTurn_neg_four K a h

/--
[uml_four_reflex_of_totalTurn_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_four_reflex_of_totalTurn_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : totalTurnZ K a.1 (dartOrbitPeriod K a) = 4) :
-- imply
  4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uml_four_reflex_of_totalTurn_four K a h

/--
[uml_four_convex_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_four_convex_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  4 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨ 4 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uml_four_convex_of_fullRevolution K a h

/--
[uml_one_le_convex_of_fullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_one_le_convex_of_fullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : TurningIsFullRevolution K a) :
-- imply
  1 ≤ leftCornerCount K a.1 (dartOrbitPeriod K a) ∨ 1 ≤ rightCornerCount K a.1 (dartOrbitPeriod K a) := by
-- proof
  apply StatMech.Lattice.uml_one_le_convex_of_fullRevolution K a h

/--
[uml_unitCell_totalTurn_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_unitCell_totalTurn_neg_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.uml_unitCell_totalTurn_neg_four

/--
[uml_unitCell_four_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_unitCell_four_convex_eq :
-- imply
  4 ≤ leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.uml_unitCell_four_convex

/--
[uml_unitCell_convex_minus_reflex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_unitCell_convex_minus_reflex_eq :
-- imply
  leftCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) - rightCornerCount unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 := by
-- proof
  apply StatMech.Lattice.uml_unitCell_convex_minus_reflex

/--
[uml_starHull_four_corners_of_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_starHull_four_corners_of_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : BalanceIsFour (ndt_StarHull K) a) :
-- imply
  4 ≤ leftCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) ∨ 4 ≤ rightCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Lattice.uml_starHull_four_corners_of_balanceIsFour K a h

/--
[uml_starHull_four_convex_of_totalTurn_neg_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/umlturning.lean)
-/
@[path]
private lemma uml_starHull_four_convex_of_totalTurn_neg_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
-- imply
  4 ≤ leftCornerCount (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Lattice.uml_starHull_four_convex_of_totalTurn_neg_four K a h


-- created on 2026-10-23
