import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jwd_gaussbonnetquant
open SimpleGraph Function StatMech StatMech.Walls


/--
[jwd_totalTurn_quantised_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_totalTurn_quantised_of_closed_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ}
-- given
  (hp : (dartNext K)^[p] e = e) :
-- imply
  ∃ k : ℤ, totalTurnZ K e p = 4 * k := by
-- proof
  apply StatMech.Walls.jwd_totalTurn_quantised_of_closed K e p hp

/--
[jwd_gaussBonnet_quantisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_gaussBonnet_quantisation_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a := by
-- proof
  apply StatMech.Walls.jwd_gaussBonnet_quantisation K a

/--
[jwd_revCount_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_revCount_spec_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a ∧ ∀ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k → k = revCount K a := by
-- proof
  apply StatMech.Walls.jwd_revCount_spec K a

/--
[jwd_curvature_sum_eq_four_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_curvature_sum_eq_four_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (∑ i ∈ Finset.range (dartOrbitPeriod K a), gbCurvature K ((dartNext K)^[i] a.1)) = 4 * revCount K a := by
-- proof
  apply StatMech.Walls.jwd_curvature_sum_eq_four_revCount K a

/--
[jwd_totalTurn_eq_four_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_totalTurn_eq_four_mul_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ k : ℤ, totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * k := by
-- proof
  apply StatMech.Walls.jwd_totalTurn_eq_four_mul K a

/--
[jwd_unitCell_totalTurn_gbq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_unitCell_totalTurn_gbq_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = -4 := by
-- proof
  apply StatMech.Walls.jwd_unitCell_totalTurn_gbq

/--
[jwd_unitCell_quantisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_unitCell_quantisation_eq :
-- imply
  totalTurnZ unitCell ucBase.1 (dartOrbitPeriod unitCell ucBase) = 4 * revCount unitCell ucBase ∧ revCount unitCell ucBase = -1 := by
-- proof
  apply StatMech.Walls.jwd_unitCell_quantisation

/--
[jwd_domino_totalTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_domino_totalTurn_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = -4 := by
-- proof
  apply StatMech.Walls.jwd_domino_totalTurn

/--
[jwd_domino_quantisation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jwd_gaussbonnetquant.lean)
-/
@[path]
private lemma jwd_domino_quantisation_eq :
-- imply
  totalTurnZ domino dmBase.1 (dartOrbitPeriod domino dmBase) = 4 * revCount domino dmBase ∧ revCount domino dmBase = -1 := by
-- proof
  apply StatMech.Walls.jwd_domino_quantisation


-- created on 2026-10-23
