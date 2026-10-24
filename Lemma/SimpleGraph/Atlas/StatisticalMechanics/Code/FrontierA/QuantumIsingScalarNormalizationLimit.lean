import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingScalarNormalizationLimit
open Filter Set StatMech StatMech.FrontierA


/--
[quantumIsingTrotterScalarNormalization_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingScalarNormalizationLimit.lean)
-/
@[path]
private lemma quantumIsingTrotterScalarNormalization_tendsto_zero_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n : Nat => (n + 1 : Real) * Real.log (1 - (beta * h / (2 * (n + 1 : Real))) ^ 2)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterScalarNormalization_tendsto_zero beta h hbeta hh


-- created on 2026-10-23
