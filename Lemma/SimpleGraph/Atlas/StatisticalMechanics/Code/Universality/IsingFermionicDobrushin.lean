import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicDobrushin.Part8
open Finset Complex StatMech StatMech.Universality StatMech.Universality.FKIsingDobrushinDomain StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable


/--
[fkIsingCriticalParameter_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fkIsingCriticalParameter_mem_Ioo_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M} :
-- imply
  fkIsingCriticalParameter ∈ Set.Ioo (0 : Real) 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fkIsingCriticalParameter_mem_Ioo P M D

/--
[criticalMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma criticalMass_nonneg_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {omega : ConfigSpace (Sym2 P.V)} :
-- imply
  0 <= D.criticalMass omega := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.criticalMass_nonneg P M D omega

/--
[criticalMass_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma criticalMass_sum_eq_one_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M} :
-- imply
  ∑ omega : ConfigSpace (Sym2 P.V), D.criticalMass omega = 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.criticalMass_sum_eq_one P M D

/--
[norm_windingPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma norm_windingPhase_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : M} :
-- imply
  ‖D.windingPhase omega e‖ = 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.norm_windingPhase P M D omega e

/--
[explorationMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma explorationMass_nonneg_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {e : M} :
-- imply
  0 ≤ D.explorationMass e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.explorationMass_nonneg P M D e

/--
[explorationMass_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma explorationMass_le_one_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {e : M} :
-- imply
  D.explorationMass e ≤ 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.explorationMass_le_one P M D e

/--
[fermionicObservable_eq_explorationMass_mul_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicObservable_eq_explorationMass_mul_phase_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {e : M}
  {phase : Complex}
-- given
  (hphase : ∀ omega, e ∈ D.exploration omega → D.windingPhase omega e = phase) :
-- imply
  D.fermionicObservable e = (D.explorationMass e : Complex) * phase := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fermionicObservable_eq_explorationMass_mul_phase P M D e phase hphase

/--
[exists_nonnegative_boundary_square_of_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma exists_nonnegative_boundary_square_of_phase_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {e : M}
  {normal phase : Complex}
  {r : Real}
-- given
  (hphase : ∀ omega, e ∈ D.exploration omega → D.windingPhase omega e = phase)
  (hr : 0 ≤ r)
  (hline : normal * phase ^ 2 = (r : Complex)) :
-- imply
  ∃ t : Real, 0 ≤ t ∧ normal * D.fermionicObservable e ^ 2 = (t : Complex) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.exists_nonnegative_boundary_square_of_phase P M D e normal phase r hphase hr hline

/--
[fermionicSummand_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicSummand_norm_le_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {omega : ConfigSpace (Sym2 P.V)}
  {e : M} :
-- imply
  ‖D.fermionicSummand omega e‖ <= D.criticalMass omega := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fermionicSummand_norm_le P M D omega e

/--
[norm_fermionicObservable_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma norm_fermionicObservable_le_one_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {e : M} :
-- imply
  ‖D.fermionicObservable e‖ <= 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.norm_fermionicObservable_le_one P M D e

/--
[fermionicObservable_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicObservable_terminal_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M} :
-- imply
  D.fermionicObservable D.terminalEdge = 1 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.fermionicObservable_terminal P M D

/--
[norm_normalizedFermionicObservable_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma norm_normalizedFermionicObservable_le_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {delta : Real}
  {e : M}
-- given
  (hdelta : 0 < delta) :
-- imply
  ‖D.normalizedFermionicObservable delta e‖ <= 1 / Real.sqrt (2 * delta) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.norm_normalizedFermionicObservable_le P M D delta hdelta e

/--
[normalizedFermionicObservable_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma normalizedFermionicObservable_terminal_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {delta : Real} :
-- imply
  D.normalizedFermionicObservable delta D.terminalEdge = 1 / (Real.sqrt (2 * delta) : Complex) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.normalizedFermionicObservable_terminal P M D delta

/--
[pairedContribution_switchingAmplitude](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma pairedContribution_switchingAmplitude_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable}
  {omega : ConfigSpace (Sym2 P.V)}
  {k : Fin 4} :
-- imply
  D.fermionicSummand omega (T.edges k) + D.fermionicSummand (T.toggle omega) (T.edges k) = isingF k (switchingAmplitude D T omega) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.pairedContribution_switchingAmplitude P M D T omega k

/--
[fermionicObservable_eq_medialVertex_edgeObs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicObservable_eq_medialVertex_edgeObs_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable}
  {k : Fin 4} :
-- imply
  D.fermionicObservable (T.edges k) = (medialVertex D T).edgeObs k := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.fermionicObservable_eq_medialVertex_edgeObs P M D T k

/--
[localFaceObservable_sideValues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma localFaceObservable_sideValues_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable}
  {v d : Complex}
-- given
  (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
  (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
-- imply
  localFaceObservable D T v d ((isingFace v d 0 + isingFace v d 1) / 2) = D.fermionicObservable (T.edges 0) ∧ localFaceObservable D T v d ((isingFace v d 1 + isingFace v d 2) / 2) = D.fermionicObservable (T.edges 3) ∧ localFaceObservable D T v d ((isingFace v d 2 + isingFace v d 3) / 2) = D.fermionicObservable (T.edges 1) ∧ localFaceObservable D T v d ((isingFace v d 3 + isingFace v d 0) / 2) = D.fermionicObservable (T.edges 2) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.localFaceObservable_sideValues P M D T v d hpq hpr hps hqr hqs hrs

/--
[localFaceObservable_contour_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma localFaceObservable_contour_zero_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable}
  {v d : Complex}
-- given
  (hpq : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 1 + isingFace v d 2) / 2)
  (hpr : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hps : (isingFace v d 0 + isingFace v d 1) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hqr : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 2 + isingFace v d 3) / 2)
  (hqs : (isingFace v d 1 + isingFace v d 2) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2)
  (hrs : (isingFace v d 2 + isingFace v d 3) / 2 ≠ (isingFace v d 3 + isingFace v d 0) / 2) :
-- imply
  isingContour (localFaceObservable D T v d) (isingFace v d) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.localFaceObservable_contour_zero P M D T v d hpq hpr hps hqr hqs hrs

/--
[fermionicObservable_sHolo_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicObservable_sHolo_relation_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable} :
-- imply
  D.fermionicObservable (T.edges 0) + D.fermionicObservable (T.edges 1) = D.fermionicObservable (T.edges 2) + D.fermionicObservable (T.edges 3) := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.fermionicObservable_sHolo_relation P M D T

/--
[fermionicObservable_contourCombination_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicDobrushin.lean)
-/
@[path]
private lemma fermionicObservable_contourCombination_zero_eq
  {P : PlanarZ2Subgraph}
  {M : Type*}
  [Fintype M]
  [DecidableEq M]
  {P M}
  {D : FKIsingDobrushinDomain P M}
  {T : D.LocalSwitchingTable} :
-- imply
  D.fermionicObservable (T.edges 0) - D.fermionicObservable (T.edges 1) + Complex.I * D.fermionicObservable (T.edges 3) - Complex.I * D.fermionicObservable (T.edges 2) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.LocalSwitchingTable.fermionicObservable_contourCombination_zero P M D T


-- created on 2026-10-23
