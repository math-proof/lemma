import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicAsymptotic
open Filter Set StatMech StatMech.FrontierA


/--
[quantumIsingTrotter_arcosh_scaled_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicAsymptotic.lean)
-/
@[path]
private lemma quantumIsingTrotter_arcosh_scaled_tendsto_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta)
  (hdisp : 0 < quantumIsingDispersion h k) :
-- imply
  Tendsto (fun n : Nat => (n + 1 : Real) * Real.arcosh (quantumIsingTrotterReducedParameter beta h (n + 1) k)) atTop (nhds (beta / 2 * quantumIsingDispersion h k)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotter_arcosh_scaled_tendsto beta h k hbeta hdisp

/--
[eventually_one_lt_quantumIsingTrotterReducedParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicAsymptotic.lean)
-/
@[path]
private lemma eventually_one_lt_quantumIsingTrotterReducedParameter_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta)
  (hdisp : 0 < quantumIsingDispersion h k) :
-- imply
  ∀ᶠ n in atTop, 1 < quantumIsingTrotterReducedParameter beta h (n + 1) k := by
-- proof
  apply StatMech.FrontierA.eventually_one_lt_quantumIsingTrotterReducedParameter beta h k hbeta hdisp

/--
[quantumIsingAntiperiodicLogSum_tendsto_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicAsymptotic.lean)
-/
@[path]
private lemma quantumIsingAntiperiodicLogSum_tendsto_raw_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta)
  (hdisp : 0 < quantumIsingDispersion h k) :
-- imply
  Tendsto (fun n : Nat => (∑ j ∈ Finset.range (n + 1), Real.log (quantumIsingTrotterReducedParameter beta h (n + 1) k - Real.cos (quantumIsingAntiperiodicAngle (n + 1) j))) + (n + 1 : Real) * Real.log 2) atTop (nhds (beta / 2 * quantumIsingDispersion h k + 2 * Real.log (1 + Real.exp (-(beta / 2 * quantumIsingDispersion h k))))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingAntiperiodicLogSum_tendsto_raw beta h k hbeta hdisp

/--
[quantumIsingAntiperiodicLogSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicAsymptotic.lean)
-/
@[path]
private lemma quantumIsingAntiperiodicLogSum_tendsto_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta)
  (hdisp : 0 < quantumIsingDispersion h k) :
-- imply
  Tendsto (fun n : Nat => (∑ j ∈ Finset.range (n + 1), Real.log (quantumIsingTrotterReducedParameter beta h (n + 1) k - Real.cos (quantumIsingAntiperiodicAngle (n + 1) j))) + (n + 1 : Real) * Real.log 2) atTop (nhds (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingAntiperiodicLogSum_tendsto beta h k hbeta hdisp


-- created on 2026-10-23
