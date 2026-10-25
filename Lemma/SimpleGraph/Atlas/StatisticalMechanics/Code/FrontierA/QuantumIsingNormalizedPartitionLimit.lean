import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingNormalizedPartitionLimit.Part2
open Filter StatMech StatMech.FrontierA


/--
[quantumIsingElevenSectorHalfLogDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingElevenSectorHalfLogDensity_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n : Nat ↦ (1 / 2 : Real) * quantumIsingElevenSectorLogDensity beta h n) atTop (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingElevenSectorHalfLogDensity_tendsto beta h hbeta hh

/--
[quantumIsingNormalizedDiagonalLogDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingNormalizedDiagonalLogDensity_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingNormalizedDiagonalLogDensity beta h) atTop (nhds ((1 / 2 : Real) * ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedDiagonalLogDensity_tendsto beta h hbeta hh

/--
[quantumIsingNormalizedDiagonalPartition_eq_pathPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingNormalizedDiagonalPartition_eq_pathPartition_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hpos : 0 < beta * h / (2 * L)) :
-- imply
  quantumIsingNormalizedDiagonalPartition beta h L = quantumIsingTrotterPathPartition beta h L L := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedDiagonalPartition_eq_pathPartition beta h L hpos

/--
[quantumIsingPeriodicTrotterAction_eq_log_pathPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingPeriodicTrotterAction_eq_log_pathPartition_eq
  {n L : Nat}
-- given
  (beta h : Real)
  (hL : L ≠ 0) :
-- imply
  quantumIsingPeriodicTrotterAction beta h n L = -Real.log (quantumIsingTrotterPathPartition beta h n L) / beta := by
-- proof
  apply StatMech.FrontierA.quantumIsingPeriodicTrotterAction_eq_log_pathPartition beta h n L hL

/--
[quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity_eq
  {n : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  quantumIsingCofinalPeriodicTrotterFreeEnergy beta h n = -quantumIsingNormalizedDiagonalLogDensity beta h n / beta := by
-- proof
  apply StatMech.FrontierA.quantumIsingCofinalPeriodicTrotterFreeEnergy_eq_logDensity beta h n hbeta hh

/--
[quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingCofinalPeriodicTrotterFreeEnergy beta h) atTop (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingCofinalPeriodicTrotterFreeEnergy_tendsto beta h hbeta hh

/--
[quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n : Nat ↦ quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop (nhds (-((1 / 2 : Real) * ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) / beta)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_raw beta h hbeta hh

/--
[quantumIsing_half_modeIntegral_eq_logPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsing_half_modeIntegral_eq_logPressure_eq
-- given
  (beta h : Real) :
-- imply
  (1 / 2 : Real) * ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)) = Real.log 2 + (1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
-- proof
  apply StatMech.FrontierA.quantumIsing_half_modeIntegral_eq_logPressure beta h

/--
[quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingNormalizedPartitionLimit.lean)
-/
@[path]
private lemma quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n : Nat ↦ quantumIsingTrotterThermodynamicFreeEnergy beta h (n + 3)) atTop (nhds (quantumIsingFreeEnergyValue beta h)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingCofinalTrotterThermodynamicFreeEnergy_tendsto beta h hbeta hh


-- created on 2026-10-23
