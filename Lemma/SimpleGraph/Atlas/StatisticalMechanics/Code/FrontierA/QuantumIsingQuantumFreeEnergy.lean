import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingQuantumFreeEnergy
open Filter StatMech StatMech.FrontierA


/--
[quantumIsingBoltzmannGenerator_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingBoltzmannGenerator_isHermitian_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  (quantumIsingBoltzmannGenerator beta h L).IsHermitian := by
-- proof
  apply StatMech.FrontierA.quantumIsingBoltzmannGenerator_isHermitian beta h L

/--
[quantumIsingChainInteraction_const_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingChainInteraction_const_false_eq
  {L : Nat} :
-- imply
  quantumIsingChainInteraction L (fun _ ↦ false) = L := by
-- proof
  apply StatMech.FrontierA.quantumIsingChainInteraction_const_false L

/--
[quantumIsingTrotterTransferKernel_const_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferKernel_const_false_eq
  {n L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingTrotterTransferKernel beta h n L (fun _ ↦ false) (fun _ ↦ false) = Real.exp (beta / (4 * n) * L) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferKernel_const_false beta h n L

/--
[quantumIsingTrotterPathPartition_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingTrotterPathPartition_lower_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hn : n ≠ 0)
  (hbeta : 0 ≤ beta)
  (hbh : 0 ≤ beta * h) :
-- imply
  Real.exp (beta * L / 4) ≤ quantumIsingTrotterPathPartition beta h n L := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterPathPartition_lower beta h n L hn hbeta hbh

/--
[quantumIsingQuantumPartition_re_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_re_pos_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  0 < (quantumIsingQuantumPartition beta h L).re := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_re_pos beta h L hbeta hh

/--
[quantumIsingQuantumPartition_norm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingQuantumFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_norm_pos_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  0 < ‖quantumIsingQuantumPartition beta h L‖ := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_norm_pos beta h L hbeta hh


-- created on 2026-10-23
