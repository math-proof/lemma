import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgePointwiseCutCounterexample.Part3
open Finset StatMech StatMech.Ising


/--
[fourBridgePointwiseCutCounterexampleWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleWeight_sum_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgePointwiseCutCounterexampleWeight P) = 3 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleWeight_sum

/--
[fourBridgePointwiseCutCounterexampleWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleWeight_logSupermodular_eq :
-- imply
  ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset, ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgePointwiseCutCounterexampleWeight P * fourBridgePointwiseCutCounterexampleWeight Q <= fourBridgePointwiseCutCounterexampleWeight (P ∩ Q) * fourBridgePointwiseCutCounterexampleWeight (P ∪ Q) := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleWeight_logSupermodular

/--
[fourBridgePointwiseCutCounterexampleWeight_complementRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleWeight_complementRatio_eq :
-- imply
  ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset, ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset, P ⊆ Q -> fourBridgePointwiseCutCounterexampleWeight P * fourBridgePointwiseCutCounterexampleWeight ((Finset.univ : Finset (Fin 4)) \ Q) <= fourBridgePointwiseCutCounterexampleWeight Q * fourBridgePointwiseCutCounterexampleWeight ((Finset.univ : Finset (Fin 4)) \ P) := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleWeight_complementRatio

/--
[fourBridgePointwiseCutCounterexampleMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleMass_nonneg_eq
  {P : Finset (Fin 4)} :
-- imply
  0 <= fourBridgePointwiseCutCounterexampleMass P := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleMass_nonneg P

/--
[fourBridgePointwiseCutCounterexampleMass_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleMass_sum_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgePointwiseCutCounterexampleMass P) = 1 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleMass_sum

/--
[fourBridgePointwiseCutCounterexampleMass_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleMass_logSupermodular_eq
  {P Q : Finset (Fin 4)}
-- given
  (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
  (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
-- imply
  fourBridgePointwiseCutCounterexampleMass P * fourBridgePointwiseCutCounterexampleMass Q <= fourBridgePointwiseCutCounterexampleMass (P ∩ Q) * fourBridgePointwiseCutCounterexampleMass (P ∪ Q) := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleMass_logSupermodular hP hQ

/--
[fourBridgePointwiseCutCounterexampleMass_complementRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexampleMass_complementRatio_eq
  {P Q : Finset (Fin 4)}
-- given
  (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
  (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset)
  (hPQ : P ⊆ Q) :
-- imply
  fourBridgePointwiseCutCounterexampleMass P * fourBridgePointwiseCutCounterexampleMass ((Finset.univ : Finset (Fin 4)) \ Q) <= fourBridgePointwiseCutCounterexampleMass Q * fourBridgePointwiseCutCounterexampleMass ((Finset.univ : Finset (Fin 4)) \ P) := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexampleMass_complementRatio hP hQ hPQ

/--
[fourBridgePointwiseCutCounterexample_rankWeights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_rankWeights_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 0 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 1 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 2 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 3 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 0 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 4 then fourBridgePointwiseCutCounterexampleWeight P else 0) = 1 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_rankWeights

/--
[fourBridgePointwiseCutCounterexample_fourierRecovery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_fourierRecovery_eq :
-- imply
  let p0 : Real := 0 let p1 : Real := 1 / 3 let p2 : Real := 1 / 3 let p3 : Real := 0 let p4 : Real := 1 / 3 fourBridgePointwiseCutCounterexampleA = 4 * (p4 - p0) + 2 * (p3 - p1) ∧ fourBridgePointwiseCutCounterexampleB = 6 * (p0 + p4) - 2 * p2 ∧ fourBridgePointwiseCutCounterexampleC = 4 * (p4 - p0) + 2 * (p1 - p3) ∧ fourBridgePointwiseCutCounterexampleD = p0 - p1 + p2 - p3 + p4 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_fourierRecovery

/--
[fourBridgePointwiseCutCounterexample_numerator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_numerator_eq_eq :
-- imply
  fourBridgeSecondMiddleNumerator fourBridgePointwiseCutCounterexampleA fourBridgePointwiseCutCounterexampleB fourBridgePointwiseCutCounterexampleC fourBridgePointwiseCutCounterexampleD = -(64 / 9) := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_numerator_eq

/--
[fourBridgePointwiseCutCounterexample_numerator_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_numerator_neg_eq :
-- imply
  fourBridgeSecondMiddleNumerator fourBridgePointwiseCutCounterexampleA fourBridgePointwiseCutCounterexampleB fourBridgePointwiseCutCounterexampleC fourBridgePointwiseCutCounterexampleD < 0 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_numerator_neg

/--
[fourBridgePointwiseCutCounterexample_not_strictlyPositive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgePointwiseCutCounterexample.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_not_strictlyPositive_eq :
-- imply
  fourBridgePointwiseCutCounterexampleMass (∅ : Finset (Fin 4)) = 0 := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_not_strictlyPositive


-- created on 2026-10-23
