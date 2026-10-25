import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.TotalTurnFour.Part2
open SimpleGraph Function Set Finset StatMech StatMech.Lattice


/--
[ttf_four_dvd_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_four_dvd_totalTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  (4 : ℤ) ∣ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Lattice.ttf_four_dvd_totalTurn K a

/--
[ttf_abs_totalTurn_le_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_abs_totalTurn_le_period_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  |totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a)| ≤ (dartOrbitPeriod (ndt_StarHull K) a : ℤ) := by
-- proof
  apply StatMech.Lattice.ttf_abs_totalTurn_le_period K a

/--
[ttf_localTurn_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_localTurn_mem_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
  {f : Site 2} :
-- imply
  usc_localTurn (ndt_StarHull K) a f = 1 ∨ usc_localTurn (ndt_StarHull K) a f = 0 ∨ usc_localTurn (ndt_StarHull K) a f = -1 := by
-- proof
  apply StatMech.Lattice.ttf_localTurn_mem K a f

/--
[ttf_totalTurn_eq_sum_localTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_totalTurn_eq_sum_localTurn_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = ∑ f ∈ usc_orbitFaces (ndt_StarHull K) a, usc_localTurn (ndt_StarHull K) a f := by
-- proof
  apply StatMech.Lattice.ttf_totalTurn_eq_sum_localTurn K a

/--
[ttf_totalTurn_eq_four_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_totalTurn_eq_four_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hmax : ttf_WindsAtMostOnce K a)
  (hmin : ttf_WindsAtLeastOnce K a) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.ttf_totalTurn_eq_four_of_winds K a hmax hmin

/--
[ttf_turningIsFullRevolution_of_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_turningIsFullRevolution_of_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hmax : ttf_WindsAtMostOnce K a)
  (hmin : ttf_WindsAtLeastOnce K a) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ttf_turningIsFullRevolution_of_winds K a hmax hmin

/--
[ttf_winds_of_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_winds_of_totalTurn_eq_four_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) :
-- imply
  ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a := by
-- proof
  apply StatMech.Lattice.ttf_winds_of_totalTurn_eq_four K a h

/--
[ttf_winds_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_winds_iff_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) ↔ (totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4) := by
-- proof
  apply StatMech.Lattice.ttf_winds_iff K a

/--
[ttf_totalTurn_eq_four_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_totalTurn_eq_four_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
  (h : EulerCharOne (ndt_StarHull K) a) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ttf_totalTurn_eq_four_of_eulerCharOne K a hp h

/--
[ttf_eulerCharOne_iff_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_eulerCharOne_iff_winds_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
-- imply
  EulerCharOne (ndt_StarHull K) a ↔ (ttf_WindsAtMostOnce K a ∧ ttf_WindsAtLeastOnce K a) := by
-- proof
  apply StatMech.Lattice.ttf_eulerCharOne_iff_winds K a hp

/--
[ttf_totalTurn_eq_four_of_balancePreservingContraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_totalTurn_eq_four_of_balancePreservingContraction_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hcontr : BalancePreservingContraction) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.ttf_totalTurn_eq_four_of_balancePreservingContraction K hSK hne a hcontr

/--
[ttf_unitCell_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_unitCell_totalTurn_eq_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.ttf_unitCell_totalTurn_eq_four

/--
[ttf_unitCell_winds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_unitCell_winds_eq :
-- imply
  |totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase)| ≤ 4 ∧ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) ≠ 0 := by
-- proof
  apply StatMech.Lattice.ttf_unitCell_winds

/--
[ttf_domino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TotalTurnFour.lean)
-/
@[path]
private lemma ttf_domino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨ totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Lattice.ttf_domino_totalTurn_eq_four


-- created on 2026-10-23
