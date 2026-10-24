import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.StarHullTurning
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[sht_starHull_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_starHull_finite_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (ndt_StarHull K).Finite := by
-- proof
  apply StatMech.Lattice.sht_starHull_finite K hK

/--
[sht_starHull_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_starHull_nonempty_eq
  {K : Set (Site 2)}
-- given
  (hne : K.Nonempty) :
-- imply
  (ndt_StarHull K).Nonempty := by
-- proof
  apply StatMech.Lattice.sht_starHull_nonempty K hne

/--
[sht_starHull_period_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_starHull_period_ge_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  3 ≤ dartOrbitPeriod (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.sht_starHull_period_ge_three K hK a

/--
[sht_starHull_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_starHull_orbit_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite) :
-- imply
  ((dartOrbitFaceWalk (ndt_StarHull K) a.1 a.2 (dartOrbitPeriod (ndt_StarHull K) a)).copy rfl (by rw [orbit_iterate_period_eq (ndt_StarHull K) a])).IsCycle := by
-- proof
  apply StatMech.Lattice.sht_starHull_orbit_isCycle K hK a

/--
[sht_vec2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_vec2_eq_eq
  {a b c d : ℤ} :
-- imply
  (![a, b] : Site 2) = ![c, d] ↔ a = c ∧ b = d := by
-- proof
  apply StatMech.Lattice.sht_vec2_eq a b c d

/--
[sht_cutWitness_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_kingSaturated_eq :
-- imply
  npm_KingSaturated cutWitness := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_kingSaturated

/--
[sht_cutWitness_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_finite_eq :
-- imply
  cutWitness.Finite := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_finite

/--
[sht_cutWitness_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_nonempty_eq :
-- imply
  cutWitness.Nonempty := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_nonempty

/--
[sht_cutWitness_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_orbit_isCycle_eq
  {a : {e : Dart // IsBoundaryDart cutWitness e}} :
-- imply
  ((dartOrbitFaceWalk cutWitness a.1 a.2 (dartOrbitPeriod cutWitness a)).copy rfl (by rw [orbit_iterate_period_eq cutWitness a])).IsCycle := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_orbit_isCycle a

/--
[sht_cutWitness_extreme_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_extreme_convex_eq :
-- imply
  turnZ cutWitness (leftDart ![1, 1]) = -1 := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_extreme_convex

/--
[sht_cutWitness_convex_corner_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cutWitness_convex_corner_disconnects_eq :
-- imply
  ¬ CellConnected (cutWitness \ {![1, 1]}) := by
-- proof
  apply StatMech.Lattice.sht_cutWitness_convex_corner_disconnects

/--
[sht_kingSat_singleCycle_convex_corner_can_disconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_kingSat_singleCycle_convex_corner_can_disconnect_eq :
-- imply
  ∃ (K : Set (Site 2)) (c : Site 2), K.Finite ∧ K.Nonempty ∧ npm_KingSaturated K ∧ IsExtremeCell K c ∧ turnZ K (leftDart c) = -1 ∧ ¬ CellConnected (K \ {c}) := by
-- proof
  apply StatMech.Lattice.sht_kingSat_singleCycle_convex_corner_can_disconnect

/--
[sht_totalTurn_eq_four_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_totalTurn_eq_four_of_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty)
  (hsat : bpc_BalanceSaturatingContraction) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.sht_totalTurn_eq_four_of_saturating K hK hne a hsat

/--
[sht_totalTurn_eq_four_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_totalTurn_eq_four_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hK : K.Finite)
  (h : EulerCharOne (ndt_StarHull K) a) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Lattice.sht_totalTurn_eq_four_of_eulerCharOne K hK a h

/--
[sht_cornerBalance_eq_four_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_cornerBalance_eq_four_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}} :
-- imply
  cornerBalance (ndt_StarHull K) a = 4 * revCount (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.sht_cornerBalance_eq_four_revCount K a

/--
[sht_contraction_of_not_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_contraction_of_not_saturating_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hcK : c ∈ K)
  (hc : c ∉ bpc_orbitFootprint K a) :
-- imply
  ∃ (K' : Set (Site 2)) (_ : K'.Finite) (_ : K'.Nonempty) (a' : {e : Dart // IsBoundaryDart K' e}), K'.ncard < K.ncard ∧ cornerBalance K' a' = cornerBalance K a := by
-- proof
  apply StatMech.Lattice.sht_contraction_of_not_saturating K hK a c hcK hc

/--
[sht_balancePreservingContraction_of_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_balancePreservingContraction_of_saturating_eq
-- given
  (h : bpc_BalanceSaturatingContraction) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Lattice.sht_balancePreservingContraction_of_saturating h

/--
[sht_unitCell_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_unitCell_totalTurn_eq_four_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 ∨ totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Lattice.sht_unitCell_totalTurn_eq_four

/--
[sht_domino_totalTurn_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullTurning.lean)
-/
@[path]
private lemma sht_domino_totalTurn_eq_four_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 ∨ totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Lattice.sht_domino_totalTurn_eq_four


-- created on 2026-10-23
