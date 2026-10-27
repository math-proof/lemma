import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
open StatMech StatMech.FrontierA


/--
[quantumIsingBlockEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockEquiv_apply_eq
  {k L : Nat}
  {sigma : QuantumIsingChainConfig (k * L)}
  {b : Fin k}
  {i : Fin L} :
-- imply
  quantumIsingBlockEquiv k L sigma b i = sigma (finProdFinEquiv (b, i)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockEquiv_apply k L sigma b i

/--
[cyclicSucc_finProd_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma cyclicSucc_finProd_castSucc_eq
  {k L : Nat}
  {b : Fin (k + 1)}
  {i : Fin L} :
-- imply
  quantumIsingCyclicSucc (finProdFinEquiv (b, i.castSucc)) = finProdFinEquiv (b, i.succ) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finProd_castSucc k L b i

/--
[cyclicSucc_finProd_last_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma cyclicSucc_finProd_last_castSucc_eq
  {k L : Nat}
  {b : Fin k} :
-- imply
  quantumIsingCyclicSucc (finProdFinEquiv (b.castSucc, Fin.last L)) = finProdFinEquiv (b.succ, (0 : Fin (L + 1))) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finProd_last_castSucc k L b

/--
[cyclicSucc_finProd_last_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma cyclicSucc_finProd_last_last_eq
  {k L : Nat} :
-- imply
  quantumIsingCyclicSucc (finProdFinEquiv (Fin.last k, Fin.last L)) = finProdFinEquiv ((0 : Fin (k + 1)), (0 : Fin (L + 1))) := by
-- proof
  apply StatMech.FrontierA.cyclicSucc_finProd_last_last k L

/--
[quantumIsingBlockEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockEquiv_symm_apply_eq
  {k L : Nat}
  {sigma : QuantumIsingBlockConfig k L}
  {b : Fin k}
  {i : Fin L} :
-- imply
  (quantumIsingBlockEquiv k L).symm sigma (finProdFinEquiv (b, i)) = sigma b i := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockEquiv_symm_apply k L sigma b i

/--
[quantumIsingCyclicSucc_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingCyclicSucc_castSucc_eq
  {L : Nat}
  {i : Fin L} :
-- imply
  quantumIsingCyclicSucc i.castSucc = i.succ := by
-- proof
  apply StatMech.FrontierA.quantumIsingCyclicSucc_castSucc L i

/--
[quantumIsingCyclicSucc_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingCyclicSucc_last_eq
  {L : Nat} :
-- imply
  quantumIsingCyclicSucc (Fin.last L) = (0 : Fin (L + 1)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingCyclicSucc_last L

/--
[quantumIsingBlockPeriodicInteraction_eq_open_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockPeriodicInteraction_eq_open_add_eq
  {k L : Nat}
  {sigma : QuantumIsingBlockConfig (k + 1) (L + 1)} :
-- imply
  quantumIsingBlockPeriodicInteraction k L sigma = quantumIsingBlockOpenInteraction k L sigma + ∑ b : Fin (k + 1), quantumIsingSpinSign (sigma b (Fin.last L)) * quantumIsingSpinSign (sigma b 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockPeriodicInteraction_eq_open_add k L sigma

/--
[quantumIsingBlockLongInteraction_eq_open_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockLongInteraction_eq_open_add_eq
  {k L : Nat}
  {sigma : QuantumIsingBlockConfig (k + 1) (L + 1)} :
-- imply
  quantumIsingBlockLongInteraction k L sigma = quantumIsingBlockOpenInteraction k L sigma + quantumIsingBlockLongSeamInteraction k L sigma := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockLongInteraction_eq_open_add k L sigma

/--
[abs_quantumIsingSpinSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma abs_quantumIsingSpinSign_eq
  {s : Bool} :
-- imply
  |quantumIsingSpinSign s| = 1 := by
-- proof
  apply StatMech.FrontierA.abs_quantumIsingSpinSign s

/--
[quantumIsingBlockInteraction_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockInteraction_sub_le_eq
  {k L : Nat}
  {sigma : QuantumIsingBlockConfig (k + 1) (L + 1)} :
-- imply
  |quantumIsingBlockLongInteraction k L sigma - quantumIsingBlockPeriodicInteraction k L sigma| ≤ 2 * (k + 1 : Real) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockInteraction_sub_le k L sigma

/--
[quantumIsingBlockLongCylinderWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockLongCylinderWeight_le_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega ≤ Real.exp (beta * (k + 1) / 2) * quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockLongCylinderWeight_le beta h n k L hbeta omega

/--
[quantumIsingBlockPeriodicCylinderWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockPeriodicCylinderWeight_le_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1)}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega ≤ Real.exp (beta * (k + 1) / 2) * quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockPeriodicCylinderWeight_le beta h n k L hbeta omega

/--
[quantumIsingSpaceTimeBlockEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeBlockEquiv_apply_eq
  {n k L : Nat}
  {t : Fin n}
  {b : Fin k}
  {i : Fin L}
-- given
  (omega : Fin n -> QuantumIsingChainConfig (k * L)) :
-- imply
  quantumIsingSpaceTimeBlockEquiv n k L omega t b i = omega t (finProdFinEquiv (b, i)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeBlockEquiv_apply n k L omega t b i

/--
[quantumIsingSpaceTimeBlockEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeBlockEquiv_symm_apply_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig n k L}
  {t : Fin n}
  {b : Fin k}
  {i : Fin L} :
-- imply
  (quantumIsingSpaceTimeBlockEquiv n k L).symm omega t (finProdFinEquiv (b, i)) = omega t b i := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeBlockEquiv_symm_apply n k L omega t b i

/--
[quantumIsingClassicalCylinderWeight_blockEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderWeight_blockEquiv_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)}
-- given
  (beta h : Real) :
-- imply
  quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1)) ((quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)).symm omega) = quantumIsingBlockLongCylinderWeight beta h n k L omega := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderWeight_blockEquiv beta h n k L omega

/--
[quantumIsingBlockPeriodicCylinderWeight_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockPeriodicCylinderWeight_eq_prod_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1)}
-- given
  (beta h : Real) :
-- imply
  quantumIsingBlockPeriodicCylinderWeight beta h n k L omega = ∏ b : Fin (k + 1), quantumIsingClassicalCylinderWeight beta h n (L + 1) (fun t => omega t b) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockPeriodicCylinderWeight_eq_prod beta h n k L omega

/--
[quantumIsingSpaceTimeBlockSwapEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeBlockSwapEquiv_apply_eq
  {n k L : Nat}
  {omega : QuantumIsingSpaceTimeBlockConfig n k L}
  {b : Fin k}
  {t : Fin n} :
-- imply
  quantumIsingSpaceTimeBlockSwapEquiv n k L omega b t = omega t b := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeBlockSwapEquiv_apply n k L omega b t

/--
[quantumIsingSpaceTimeBlockSwapEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingSpaceTimeBlockSwapEquiv_symm_apply_eq
  {n k L : Nat}
  {t : Fin n}
  {b : Fin k}
-- given
  (omega : Fin k -> Fin n -> QuantumIsingChainConfig L) :
-- imply
  (quantumIsingSpaceTimeBlockSwapEquiv n k L).symm omega t b = omega b t := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpaceTimeBlockSwapEquiv_symm_apply n k L omega t b

/--
[quantumIsingBlockPeriodicCylinderWeight_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingBlockPeriodicCylinderWeight_sum_eq
  {n k L : Nat}
-- given
  (beta h : Real) :
-- imply
  (∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1), quantumIsingBlockPeriodicCylinderWeight beta h n k L omega) = quantumIsingClassicalCylinderPartition beta h n (L + 1) ^ (k + 1) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBlockPeriodicCylinderWeight_sum beta h n k L

/--
[quantumIsingClassicalCylinderPartition_block_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_block_upper_eq
  {n k L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingClassicalCylinderPartition beta h (n + 1) ((k + 1) * (L + 1)) ≤ quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^ (k + 1) * Real.exp (beta * (k + 1) / 2) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_block_upper beta h n k L hbeta

/--
[quantumIsingClassicalCylinderPartition_block_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean)
-/
@[path]
private lemma quantumIsingClassicalCylinderPartition_block_lower_eq
  {n k L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta) :
-- imply
  quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^ (k + 1) * Real.exp (-beta * (k + 1) / 2) ≤ quantumIsingClassicalCylinderPartition beta h (n + 1) ((k + 1) * (L + 1)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingClassicalCylinderPartition_block_lower beta h n k L hbeta


-- created on 2026-10-23
