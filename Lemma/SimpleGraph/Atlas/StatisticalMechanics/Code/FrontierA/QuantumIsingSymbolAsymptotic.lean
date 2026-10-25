import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSymbolAsymptotic.Part2
open Filter StatMech StatMech.FrontierA


/--
[sinh_div_tendsto_one_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean)
-/
@[path]
private lemma sinh_div_tendsto_one_right_eq :
-- imply
  Tendsto (fun t : Real => Real.sinh t / t) (𝓝[>] 0) (nhds 1) := by
-- proof
  apply StatMech.FrontierA.sinh_div_tendsto_one_right

/--
[cosh_sub_one_div_sq_tendsto_half_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean)
-/
@[path]
private lemma cosh_sub_one_div_sq_tendsto_half_right_eq :
-- imply
  Tendsto (fun t : Real => (Real.cosh t - 1) / t ^ 2) (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
-- proof
  apply StatMech.FrontierA.cosh_sub_one_div_sq_tendsto_half_right

/--
[quantumIsingReducedParameterAtScale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean)
-/
@[path]
private lemma quantumIsingReducedParameterAtScale_eq_eq
  {n : Nat}
-- given
  (beta h k : Real) :
-- imply
  quantumIsingTrotterReducedParameter beta h n k = quantumIsingReducedParameterAtScale h k (beta / (2 * n)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingReducedParameterAtScale_eq beta h k n

/--
[quantumIsingReducedParameter_scaled_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean)
-/
@[path]
private lemma quantumIsingReducedParameter_scaled_tendsto_eq
-- given
  (h k : Real) :
-- imply
  Tendsto (fun t : Real => (quantumIsingReducedParameterAtScale h k t - 1) / t ^ 2) (𝓝[>] 0) (nhds ((1 + 4 * h ^ 2 + 4 * h * Real.cos k) / 2)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingReducedParameter_scaled_tendsto h k

/--
[quantumIsingTrotterReducedParameter_scaled_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSymbolAsymptotic.lean)
-/
@[path]
private lemma quantumIsingTrotterReducedParameter_scaled_tendsto_eq
-- given
  (beta h k : Real)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n : Nat => (n + 1 : Real) ^ 2 * (quantumIsingTrotterReducedParameter beta h (n + 1) k - 1)) atTop (nhds (beta ^ 2 / 8 * quantumIsingDispersion h k ^ 2)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterReducedParameter_scaled_tendsto beta h k hbeta


-- created on 2026-10-23
