import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.Part3
open Finset StatMech StatMech.Ising


/--
[fourBridgeSecondMiddleCutCounterexampleWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexampleWeight_sum_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgeSecondMiddleCutCounterexampleWeight P) = 2824 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexampleWeight_sum

/--
[fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular_eq :
-- imply
  ∀ P ∈ (Finset.univ : Finset (Fin 4)).powerset, ∀ Q ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgeSecondMiddleCutCounterexampleWeight P * fourBridgeSecondMiddleCutCounterexampleWeight Q <= fourBridgeSecondMiddleCutCounterexampleWeight (P ∩ Q) * fourBridgeSecondMiddleCutCounterexampleWeight (P ∪ Q) := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexampleWeight_logSupermodular

/--
[fourBridgeSecondMiddleCutCounterexampleMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexampleMass_nonneg_eq
  {P : Finset (Fin 4)} :
-- imply
  0 <= fourBridgeSecondMiddleCutCounterexampleMass P := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexampleMass_nonneg P

/--
[fourBridgeSecondMiddleCutCounterexampleMass_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexampleMass_sum_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, fourBridgeSecondMiddleCutCounterexampleMass P) = 1 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexampleMass_sum

/--
[fourBridgeSecondMiddleCutCounterexampleMass_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexampleMass_logSupermodular_eq
  {P Q : Finset (Fin 4)}
-- given
  (hP : P ∈ (Finset.univ : Finset (Fin 4)).powerset)
  (hQ : Q ∈ (Finset.univ : Finset (Fin 4)).powerset) :
-- imply
  fourBridgeSecondMiddleCutCounterexampleMass P * fourBridgeSecondMiddleCutCounterexampleMass Q <= fourBridgeSecondMiddleCutCounterexampleMass (P ∩ Q) * fourBridgeSecondMiddleCutCounterexampleMass (P ∪ Q) := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexampleMass_logSupermodular hP hQ

/--
[fourBridgeSecondMiddleCutCounterexample_rankWeights](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_rankWeights_eq :
-- imply
  (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 0 then fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 16 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 1 then fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 547 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 2 then fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 1165 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 3 then fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 584 ∧ (∑ P ∈ (Finset.univ : Finset (Fin 4)).powerset, if P.card = 4 then fourBridgeSecondMiddleCutCounterexampleWeight P else 0) = 512 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_rankWeights

/--
[fourBridgeSecondMiddleCutCounterexample_fourierRecovery](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_fourierRecovery_eq :
-- imply
  let p0 : Real := 16 / 2824 let p1 : Real := 547 / 2824 let p2 : Real := 1165 / 2824 let p3 : Real := 584 / 2824 let p4 : Real := 512 / 2824 fourBridgeSecondMiddleCutCounterexampleA = 4 * (p4 - p0) + 2 * (p3 - p1) ∧ fourBridgeSecondMiddleCutCounterexampleB = 6 * (p0 + p4) - 2 * p2 ∧ fourBridgeSecondMiddleCutCounterexampleC = 4 * (p4 - p0) + 2 * (p1 - p3) ∧ fourBridgeSecondMiddleCutCounterexampleD = p0 - p1 + p2 - p3 + p4 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_fourierRecovery

/--
[fourBridgeSecondMiddleCutCounterexample_scalarBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_scalarBounds_eq :
-- imply
  let a := fourBridgeSecondMiddleCutCounterexampleA let b := fourBridgeSecondMiddleCutCounterexampleB let c := fourBridgeSecondMiddleCutCounterexampleC let d := fourBridgeSecondMiddleCutCounterexampleD 0 <= a ∧ a <= 2 ∧ 0 <= b ∧ b <= 6 ∧ 0 <= c ∧ c <= 4 ∧ 0 <= d ∧ d <= 1 ∧ a * d <= c ∧ c * d <= a ∧ a * c <= 2 * b + 4 * d ∧ a * b <= 3 * (a + c) ∧ b * c <= 3 * (a + c) ∧ 3 * a <= 6 + b ∧ 3 * c <= 6 + b ∧ b ^ 2 <= 5 + 6 * d := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_scalarBounds

/--
[fourBridgeSecondMiddleCutCounterexample_rankQuadraticCuts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_rankQuadraticCuts_eq :
-- imply
  let p0 : Real := 16 / 2824 let p1 : Real := 547 / 2824 let p2 : Real := 1165 / 2824 let p3 : Real := 584 / 2824 let p4 : Real := 512 / 2824 p1 ^ 2 <= p1 + 2 * p0 * p2 ∧ p3 ^ 2 <= p3 + 2 * p2 * p4 ∧ p0 * p3 <= p1 * p4 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_rankQuadraticCuts

/--
[fourBridgeSecondMiddleCutCounterexample_nestedSingletonPairCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_nestedSingletonPairCut_eq :
-- imply
  let M : Finset (Fin 4) := Finset.univ let w := fourBridgeSecondMiddleCutCounterexampleWeight (w {0} + w {1}) * w (M \ {0, 1}) + (w {0} + w {2}) * w (M \ {0, 2}) + (w {0} + w {3}) * w (M \ {0, 3}) + (w {1} + w {2}) * w (M \ {1, 2}) + (w {1} + w {3}) * w (M \ {1, 3}) + (w {2} + w {3}) * w (M \ {2, 3}) <= w {0, 1} * (w (M \ {0}) + w (M \ {1})) + w {0, 2} * (w (M \ {0}) + w (M \ {2})) + w {0, 3} * (w (M \ {0}) + w (M \ {3})) + w {1, 2} * (w (M \ {1}) + w (M \ {2})) + w {1, 3} * (w (M \ {1}) + w (M \ {3})) + w {2, 3} * (w (M \ {2}) + w (M \ {3})) := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_nestedSingletonPairCut

/--
[fourBridgeSecondMiddleCutCounterexample_numerator_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_numerator_neg_eq :
-- imply
  fourBridgeSecondMiddleNumerator fourBridgeSecondMiddleCutCounterexampleA fourBridgeSecondMiddleCutCounterexampleB fourBridgeSecondMiddleCutCounterexampleC fourBridgeSecondMiddleCutCounterexampleD < 0 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_numerator_neg

/--
[fourBridgeSecondMiddleCutCounterexample_productFace_numerator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_productFace_numerator_pos_eq :
-- imply
  0 < fourBridgeSecondMiddleNumerator fourBridgeSecondMiddleCutCounterexampleA fourBridgeSecondMiddleCutCounterexampleB (fourBridgeSecondMiddleCutCounterexampleA * fourBridgeSecondMiddleCutCounterexampleD) fourBridgeSecondMiddleCutCounterexampleD := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_productFace_numerator_pos

/--
[fourBridgeSecondMiddleCutCounterexample_no_nonnegative_upperFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_no_nonnegative_upperFace_eq
  {U : Real}
-- given
  (hU : fourBridgeSecondMiddleCutCounterexampleC <= U) :
-- imply
  fourBridgeSecondMiddleNumerator fourBridgeSecondMiddleCutCounterexampleA fourBridgeSecondMiddleCutCounterexampleB U fourBridgeSecondMiddleCutCounterexampleD < 0 := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_no_nonnegative_upperFace hU

/--
[fourBridgeSecondMiddleCutCounterexample_violates_pointwiseComplementRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeSecondMiddleCutCounterexample.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_violates_pointwiseComplementRatio_eq :
-- imply
  let M : Finset (Fin 4) := Finset.univ let mu := fourBridgeSecondMiddleCutCounterexampleMass mu {1} * mu M < mu ∅ * mu (M \ {1}) := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_violates_pointwiseComplementRatio


-- created on 2026-10-23
