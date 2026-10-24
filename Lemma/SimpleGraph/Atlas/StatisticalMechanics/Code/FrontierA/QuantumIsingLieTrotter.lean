import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingLieTrotter
open Filter Matrix StatMech StatMech.FrontierA


/--
[quantumIsingTrotterStep_scaled_sub_entry_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingTrotterStep_scaled_sub_entry_tendsto_eq
  {L : Nat}
  {sigma tau : QuantumIsingChainConfig L}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => ((n + 1 : Real) : Complex) * (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real)) sigma tau - (1 : Matrix (QuantumIsingChainConfig L) (QuantumIsingChainConfig L) Complex) sigma tau)) atTop (nhds (quantumIsingBoltzmannGenerator beta h L sigma tau)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterStep_scaled_sub_entry_tendsto beta h L sigma tau

/--
[quantumIsingTrotterStep_scaled_error_norm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingTrotterStep_scaled_error_norm_tendsto_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => ‖(n + 1 : Real) • (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real)) - 1) - quantumIsingBoltzmannGenerator beta h L‖) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterStep_scaled_error_norm_tendsto beta h L

/--
[quantumIsingExponentialStep_scaled_error_norm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingExponentialStep_scaled_error_norm_tendsto_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => ‖(n + 1 : Real) • (NormedSpace.exp ((1 / (n + 1 : Real)) • quantumIsingBoltzmannGenerator beta h L) - 1) - quantumIsingBoltzmannGenerator beta h L‖) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingExponentialStep_scaled_error_norm_tendsto beta h L

/--
[quantumIsingTrotterStep_power_tendsto_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingTrotterStep_power_tendsto_exp_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => (quantumIsingTrotterStep beta h L (1 / (n + 1 : Real))) ^ (n + 1)) atTop (nhds (NormedSpace.exp (quantumIsingBoltzmannGenerator beta h L))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterStep_power_tendsto_exp beta h L

/--
[quantumIsingTrotterTransferMatrix_power_tendsto_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingTrotterTransferMatrix_power_tendsto_exp_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => (quantumIsingTrotterTransferMatrix beta h (n + 1) L) ^ (n + 1)) atTop (nhds (NormedSpace.exp (quantumIsingBoltzmannGenerator beta h L))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTransferMatrix_power_tendsto_exp beta h L

/--
[quantumIsingTrotterTrace_tendsto_quantumPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingTrotterTrace_tendsto_quantumPartition_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  Tendsto (fun n : Nat => ((quantumIsingTrotterTransferMatrix beta h (n + 1) L) ^ (n + 1)).trace) atTop (nhds (quantumIsingQuantumPartition beta h L)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterTrace_tendsto_quantumPartition beta h L

/--
[quantumIsingNormalizedClassicalCylinder_tendsto_quantumPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingLieTrotter.lean)
-/
@[path]
private lemma quantumIsingNormalizedClassicalCylinder_tendsto_quantumPartition_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hbh : 0 < beta * h) :
-- imply
  Tendsto (fun n : Nat => ((Real.exp (-quantumIsingVerticalCoupling beta h (n + 1)) ^ (L * (n + 1)) * quantumIsingClassicalCylinderPartition beta h (n + 1) L : Real) : Complex)) atTop (nhds (quantumIsingQuantumPartition beta h L)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedClassicalCylinder_tendsto_quantumPartition beta h L hbh


-- created on 2026-10-23
