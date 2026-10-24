import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.StarHullUmlaufsatz
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[shu_starHull_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_starHull_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (ndt_StarHull K).Finite := by
-- proof
  apply StatMech.Lattice.shu_starHull_finite K hK

/--
[shu_starHull_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_starHull_nonempty_eq
  {K : Set (Site 2)}
-- given
  (hne : K.Nonempty) :
-- imply
  (ndt_StarHull K).Nonempty := by
-- proof
  apply StatMech.Lattice.shu_starHull_nonempty K hne

/--
[shu_starHull_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_starHull_period_ge_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  3 ≤ dartOrbitPeriod (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_starHull_period_ge_three K hK a

/--
[shu_starHull_mpl_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_starHull_mpl_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  (mpl_orbitLoop (ndt_StarHull K) a).IsCycle := by
-- proof
  apply StatMech.Lattice.shu_starHull_mpl_isCycle K hK a

/--
[shu_turningIsFullRevolution_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_turningIsFullRevolution_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_turningIsFullRevolution_of_saturating K hK hne a hsat

/--
[shu_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.shu_totalTurn_eq_four_of_saturating K hK hne a hsat

/--
[shu_turningIsFullRevolution_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_turningIsFullRevolution_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (h : EulerCharOne (ndt_StarHull K) a) :
-- imply
  TurningIsFullRevolution (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_turningIsFullRevolution_of_eulerCharOne K hK a h

/--
[shu_totalTurn_eq_four_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_totalTurn_eq_four_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (h : EulerCharOne (ndt_StarHull K) a) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.shu_totalTurn_eq_four_of_eulerCharOne K hK a h

/--
[shu_totalTurn_eq_four_of_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_totalTurn_eq_four_of_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : BalanceIsFour (ndt_StarHull K) a) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.shu_totalTurn_eq_four_of_balanceIsFour K a h

/--
[shu_cornerBalance_eq_four_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_cornerBalance_eq_four_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  cornerBalance (ndt_StarHull K) a = 4 * revCount (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_cornerBalance_eq_four_revCount K a

/--
[shu_eulerCharOne_iff_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_eulerCharOne_iff_balanceIsFour_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  EulerCharOne (ndt_StarHull K) a ↔ BalanceIsFour (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_eulerCharOne_iff_balanceIsFour K hK a

/--
[shu_balanceIsFour_iff_revCount_pm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_balanceIsFour_iff_revCount_pm_one_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  BalanceIsFour (ndt_StarHull K) a ↔ (revCount (ndt_StarHull K) a = 1 ∨ revCount (ndt_StarHull K) a = -1) := by
-- proof
  apply StatMech.Lattice.shu_balanceIsFour_iff_revCount_pm_one K a

/--
[shu_windingWitness_of_minVertStepLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_windingWitness_of_minVertStepLeft_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shu_windingWitness_of_minVertStepLeft K hK a hres

/--
[shu_unitCell_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_unitCell_totalTurn_eq_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.shu_unitCell_totalTurn_eq_four

/--
[shu_domino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_domino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨ totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Lattice.shu_domino_totalTurn_eq_four

/--
[shu_unitCell_minVertStepLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_unitCell_minVertStepLeft_eq :
-- imply
  shw_MinVertStepLeft unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shu_unitCell_minVertStepLeft

/--
[shu_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shu_unitCell_windingWitness

/--
[shu_unitCell_balanceIsFour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullUmlaufsatz.lean)
-/
@[path]
private lemma shu_unitCell_balanceIsFour_eq :
-- imply
  BalanceIsFour unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shu_unitCell_balanceIsFour


-- created on 2026-10-23
