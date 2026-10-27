import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
open SimpleGraph Function StatMech StatMech.Lattice


/--
[gbCurvature_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma gbCurvature_mem_eq
  {K : Set (Site 2)}
  {e : Dart} :
-- imply
  gbCurvature K e = 1 ∨ gbCurvature K e = 0 ∨ gbCurvature K e = -1 := by
-- proof
  apply StatMech.Lattice.gbCurvature_mem K e

/--
[curvature_sum_eq_totalTurnZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma curvature_sum_eq_totalTurnZ_eq
  {K : Set (Site 2)}
  {e : Dart}
  {p : ℕ} :
-- imply
  totalTurnZ K e p = ∑ i ∈ Finset.range p, gbCurvature K ((dartNext K)^[i] e) := by
-- proof
  apply StatMech.Lattice.curvature_sum_eq_totalTurnZ K e p

/--
[gaussBonnet_local_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma gaussBonnet_local_global_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  totalTurnZ K a.1 (dartOrbitPeriod K a) = 4 * revCount K a := by
-- proof
  apply StatMech.Lattice.gaussBonnet_local_global K a

/--
[turningIsFullRevolution_iff_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma turningIsFullRevolution_iff_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  TurningIsFullRevolution K a ↔ (revCount K a = 1 ∨ revCount K a = -1) := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_iff_revCount K a

/--
[turningIsFullRevolution_of_revCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_revCount_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : revCount K a = 1 ∨ revCount K a = -1) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_revCount K a h

/--
[cycleGraph_card_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma cycleGraph_card_edges_eq
  {n : ℕ} :
-- imply
  (cycleGraph (n + 3)).edgeFinset.card = n + 3 := by
-- proof
  apply StatMech.Lattice.cycleGraph_card_edges n

/--
[cycleGraph_cyclomaticNumber_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma cycleGraph_cyclomaticNumber_eq_one_eq
  {n : ℕ} :
-- imply
  cyclomaticNumber (cycleGraph (n + 3)) = 1 := by
-- proof
  apply StatMech.Lattice.cycleGraph_cyclomaticNumber_eq_one n

/--
[cycleGraph_not_isAcyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma cycleGraph_not_isAcyclic_eq
  {n : ℕ} :
-- imply
  ¬ (cycleGraph (n + 3)).IsAcyclic := by
-- proof
  apply StatMech.Lattice.cycleGraph_not_isAcyclic n

/--
[orbitEnum_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma orbitEnum_injective_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  Function.Injective (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a) := by
-- proof
  apply StatMech.Lattice.orbitEnum_injective K a

/--
[contour_card_darts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma contour_card_darts_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (Finset.univ.image (fun i : Fin (dartOrbitPeriod K a) => (dartNextSub K)^[i.val] a)).card = dartOrbitPeriod K a := by
-- proof
  apply StatMech.Lattice.contour_card_darts K a

/--
[contourEulerChar_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma contourEulerChar_eq_one_eq
  {p : ℕ}
-- given
  (hp : 3 ≤ p) :
-- imply
  contourEulerChar p = 1 := by
-- proof
  apply StatMech.Lattice.contourEulerChar_eq_one hp

/--
[turningIsFullRevolution_of_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma turningIsFullRevolution_of_eulerCharOne_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (h : EulerCharOne K a) :
-- imply
  TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.turningIsFullRevolution_of_eulerCharOne K a hp h

/--
[eulerCharOne_iff_turningIsFullRevolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma eulerCharOne_iff_turningIsFullRevolution_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a) :
-- imply
  EulerCharOne K a ↔ TurningIsFullRevolution K a := by
-- proof
  apply StatMech.Lattice.eulerCharOne_iff_turningIsFullRevolution K a hp

/--
[unitCell_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma unitCell_eulerCharOne_eq :
-- imply
  EulerCharOne unitCell ucBase := by
-- proof
  apply StatMech.Lattice.unitCell_eulerCharOne

/--
[domino_eulerCharOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GaussBonnet.lean)
-/
@[path]
private lemma domino_eulerCharOne_eq :
-- imply
  EulerCharOne domino dmBase := by
-- proof
  apply StatMech.Lattice.domino_eulerCharOne


-- created on 2026-10-23
