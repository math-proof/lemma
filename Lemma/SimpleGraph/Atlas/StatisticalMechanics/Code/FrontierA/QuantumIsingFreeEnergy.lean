import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFreeEnergy
open Filter Matrix StatMech StatMech.FrontierA


/--
[quantumIsingPeriodicTrotterFreeEnergy_tendsto_finiteQuantum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingPeriodicTrotterFreeEnergy_tendsto_finiteQuantum_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hL : L ≠ 0)
  (hbeta : 0 < beta)
  (hbh : 0 < beta * h) :
-- imply
  Tendsto (fun n : Nat ↦ quantumIsingPeriodicTrotterAction beta h (n + 1) L / L) atTop (nhds (quantumIsingFiniteFreeEnergy beta h L)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingPeriodicTrotterFreeEnergy_tendsto_finiteQuantum beta h L hL hbeta hbh

/--
[quantumIsingFiniteFreeEnergy_sub_value_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_sub_value_le_eq
  {L : Nat}
-- given
  (beta h : Real)
  (hL : L ≠ 0)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  |quantumIsingFiniteFreeEnergy beta h L - quantumIsingFreeEnergyValue beta h| ≤ 1 / (2 * (L : Real)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_sub_value_le beta h L hL hbeta hh

/--
[quantumIsingFiniteFreeEnergy_tendsto_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_tendsto_of_pos_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop (nhds (quantumIsingFreeEnergyValue beta h)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_tendsto_of_pos beta h hbeta hh

/--
[quantumIsingFiniteFreeEnergy_neg_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_neg_field_eq
  {L : Nat}
-- given
  (beta h : Real) :
-- imply
  quantumIsingFiniteFreeEnergy beta (-h) L = quantumIsingFiniteFreeEnergy beta h L := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_neg_field beta h L

/--
[quantumIsingFiniteFreeEnergy_tendsto_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingFreeEnergy.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_tendsto_of_ne_zero_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : h ≠ 0) :
-- imply
  Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop (nhds (quantumIsingFreeEnergyValue beta h)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_tendsto_of_ne_zero beta h hbeta hh


-- created on 2026-10-23
