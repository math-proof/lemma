import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part7
open Filter StatMech StatMech.FrontierA


/--
[quantumIsingSumBlockEquiv_apply_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSumBlockEquiv_apply_left_eq
  {A B : Nat}
  {sigma : QuantumIsingChainConfig (A + B)}
  {i : Fin A} :
-- imply
  (quantumIsingSumBlockEquiv A B sigma).1 i = sigma (finSumFinEquiv (Sum.inl i)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSumBlockEquiv_apply_left A B sigma i

/--
[quantumIsingSumBlockEquiv_apply_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSumBlockEquiv_apply_right_eq
  {A B : Nat}
  {sigma : QuantumIsingChainConfig (A + B)}
  {j : Fin B} :
-- imply
  (quantumIsingSumBlockEquiv A B sigma).2 j = sigma (finSumFinEquiv (Sum.inr j)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSumBlockEquiv_apply_right A B sigma j

/--
[quantumIsingSumBlockEquiv_symm_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSumBlockEquiv_symm_left_eq
  {A B : Nat}
  {pair : QuantumIsingTwoBlockConfig A B}
  {i : Fin A} :
-- imply
  (quantumIsingSumBlockEquiv A B).symm pair (finSumFinEquiv (Sum.inl i)) = pair.1 i := by
-- proof
  apply StatMech.FrontierA.quantumIsingSumBlockEquiv_symm_left A B pair i

/--
[quantumIsingSumBlockEquiv_symm_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSumBlockEquiv_symm_right_eq
  {A B : Nat}
  {pair : QuantumIsingTwoBlockConfig A B}
  {j : Fin B} :
-- imply
  (quantumIsingSumBlockEquiv A B).symm pair (finSumFinEquiv (Sum.inr j)) = pair.2 j := by
-- proof
  apply StatMech.FrontierA.quantumIsingSumBlockEquiv_symm_right A B pair j

/--
[cyclicSucc_finSum_left_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma cyclicSucc_finSum_left_castSucc_eq
  {A B : Nat}
  {i : Fin A} :
-- imply
  quantumIsingCyclicSucc (finSumFinEquiv (Sum.inl i.castSucc) : Fin ((A + 1) + (B + 1))) = finSumFinEquiv (Sum.inl i.succ) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finSum_left_castSucc A B i

/--
[cyclicSucc_finSum_left_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma cyclicSucc_finSum_left_last_eq
  {A B : Nat} :
-- imply
  quantumIsingCyclicSucc (finSumFinEquiv (Sum.inl (Fin.last A)) : Fin ((A + 1) + (B + 1))) = finSumFinEquiv (Sum.inr (0 : Fin (B + 1))) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finSum_left_last A B

/--
[cyclicSucc_finSum_right_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma cyclicSucc_finSum_right_castSucc_eq
  {A B : Nat}
  {j : Fin B} :
-- imply
  quantumIsingCyclicSucc (finSumFinEquiv (Sum.inr j.castSucc) : Fin ((A + 1) + (B + 1))) = finSumFinEquiv (Sum.inr j.succ) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finSum_right_castSucc A B j

/--
[cyclicSucc_finSum_right_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma cyclicSucc_finSum_right_last_eq
  {A B : Nat} :
-- imply
  quantumIsingCyclicSucc (finSumFinEquiv (Sum.inr (Fin.last B)) : Fin ((A + 1) + (B + 1))) = finSumFinEquiv (Sum.inl (0 : Fin (A + 1))) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finSum_right_last A B

/--
[quantumIsingTwoBlockPeriodicInteraction_eq_open_seams](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockPeriodicInteraction_eq_open_seams_eq
  {A B : Nat}
  {pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)} :
-- imply
  quantumIsingTwoBlockPeriodicInteraction A B pair = quantumIsingTwoBlockOpenInteraction A B pair + quantumIsingSpinSign (pair.1 (Fin.last A)) * quantumIsingSpinSign (pair.1 0) + quantumIsingSpinSign (pair.2 (Fin.last B)) * quantumIsingSpinSign (pair.2 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockPeriodicInteraction_eq_open_seams A B pair

/--
[quantumIsingTwoBlockLongInteraction_eq_open_seams](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockLongInteraction_eq_open_seams_eq
  {A B : Nat}
  {pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)} :
-- imply
  quantumIsingTwoBlockLongInteraction A B pair = quantumIsingTwoBlockOpenInteraction A B pair + quantumIsingSpinSign (pair.1 (Fin.last A)) * quantumIsingSpinSign (pair.2 0) + quantumIsingSpinSign (pair.2 (Fin.last B)) * quantumIsingSpinSign (pair.1 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockLongInteraction_eq_open_seams A B pair

/--
[quantumIsingTwoBlockInteraction_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockInteraction_sub_le_eq
  {A B : Nat}
  {pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)} :
-- imply
  |quantumIsingTwoBlockLongInteraction A B pair - quantumIsingTwoBlockPeriodicInteraction A B pair| ≤ 4 := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockInteraction_sub_le A B pair

/--
[quantumIsingTwoBlockLongCylinderWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockLongCylinderWeight_le_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega ≤ Real.exp beta * quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockLongCylinderWeight_le beta h n A B hbeta omega

/--
[quantumIsingTwoBlockPeriodicCylinderWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockPeriodicCylinderWeight_le_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1)}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega ≤ Real.exp beta * quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockPeriodicCylinderWeight_le beta h n A B hbeta omega

/--
[quantumIsingSpaceTimeSumBlockEquiv_symm_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeSumBlockEquiv_symm_left_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n A B}
  {t : Fin n}
  {i : Fin A} :
-- imply
  (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t (finSumFinEquiv (Sum.inl i)) = (omega t).1 i := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeSumBlockEquiv_symm_left n A B omega t i

/--
[quantumIsingSpaceTimeSumBlockEquiv_symm_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeSumBlockEquiv_symm_right_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n A B}
  {t : Fin n}
  {j : Fin B} :
-- imply
  (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t (finSumFinEquiv (Sum.inr j)) = (omega t).2 j := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeSumBlockEquiv_symm_right n A B omega t j

/--
[quantumIsingSpaceTimeSumBlockEquiv_symm_castAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeSumBlockEquiv_symm_castAdd_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n A B}
  {t : Fin n}
  {i : Fin A} :
-- imply
  (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t (Fin.castAdd B i) = (omega t).1 i := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeSumBlockEquiv_symm_castAdd n A B omega t i

/--
[quantumIsingSpaceTimeSumBlockEquiv_symm_natAdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeSumBlockEquiv_symm_natAdd_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n A B}
  {t : Fin n}
  {j : Fin B} :
-- imply
  (quantumIsingSpaceTimeSumBlockEquiv n A B).symm omega t (Fin.natAdd A j) = (omega t).2 j := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeSumBlockEquiv_symm_natAdd n A B omega t j

/--
[quantumIsingClassicalCylinderWeight_sumBlockEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderWeight_sumBlockEquiv_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)}
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1)) ((quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)).symm omega) = quantumIsingTwoBlockLongCylinderWeight beta h n A B omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderWeight_sumBlockEquiv beta h n A B omega

/--
[quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul_eq
  {n A B : Nat}
  {omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1)}
-- given
  (beta h : Real) :
-- imply
  quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega = quantumIsingClassicalCylinderWeight beta h n (A + 1) (fun t => (omega t).1) * quantumIsingClassicalCylinderWeight beta h n (B + 1) (fun t => (omega t).2) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul beta h n A B omega

/--
[quantumIsingTwoBlockPeriodicCylinderWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingTwoBlockPeriodicCylinderWeight_sum_eq
  {n A B : Nat}
-- given
  (beta h : Real) :
-- imply
  (∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1), quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega) = quantumIsingClassicalCylinderPartition beta h n (A + 1) * quantumIsingClassicalCylinderPartition beta h n (B + 1) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTwoBlockPeriodicCylinderWeight_sum beta h n A B

/--
[quantumIsingClassicalCylinderPartition_add_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_add_upper_eq
  {n A B : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) ≤ Real.exp beta * (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) * quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_add_upper beta h n A B hbeta

/--
[quantumIsingClassicalCylinderPartition_add_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_add_lower_eq
  {n A B : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  Real.exp (-beta) * (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) * quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) ≤ quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_add_lower beta h n A B hbeta

/--
[quantumIsingClassicalCylinderPartition_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_pos_eq
  {n L : Nat}
-- given
  (beta h : Real) :
-- imply
  0 < quantumIsingClassicalCylinderPartition beta h n L := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_pos beta h n L

/--
[quantumIsingClassicalLogPartitionSequence_almostAdditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalLogPartitionSequence_almostAdditive_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  QuantumIsingAlmostAdditive (quantumIsingClassicalLogPartitionSequence beta h n) beta := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalLogPartitionSequence_almostAdditive beta h n hbeta

/--
[quantumIsingClassicalLogPressure_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalLogPressure_tendsto_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun L : Nat => quantumIsingClassicalLogPartitionSequence beta h n L / L) atTop (nhds (quantumIsingClassicalLogPressureLimit beta h n hbeta)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalLogPressure_tendsto beta h n hbeta

/--
[quantumIsingClassicalLogPressureLimit_sub_finite_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalLogPressureLimit_sub_finite_le_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hL : L ≠ 0) :
-- imply
  |quantumIsingClassicalLogPressureLimit beta h n hbeta - Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤ beta / L := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalLogPressureLimit_sub_finite_le beta h n L hbeta hL

/--
[quantumIsingClassicalLogPressureLimit_sub_finite_le_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean)
-/
@[path]
private lemma quantumIsingClassicalLogPressureLimit_sub_finite_le_sharp_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hL : L ≠ 0) :
-- imply
  |quantumIsingClassicalLogPressureLimit beta h n hbeta - Real.log (quantumIsingClassicalCylinderPartition beta h (n + 1) L) / L| ≤ beta / (2 * L) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalLogPressureLimit_sub_finite_le_sharp beta h n L hbeta hL


-- created on 2026-10-23
