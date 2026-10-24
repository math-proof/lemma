import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicReduction
open StatMech StatMech.FrontierA


/--
[quantumIsingSpectralRoot_gt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma quantumIsingSpectralRoot_gt_one_eq
  {a : Real}
-- given
  (ha : 1 < a) :
-- imply
  1 < quantumIsingSpectralRoot a := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpectralRoot_gt_one ha

/--
[quantumIsingSpectralRoot_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma quantumIsingSpectralRoot_inv_eq
  {a : Real}
-- given
  (ha : 1 ≤ a) :
-- imply
  (quantumIsingSpectralRoot a)⁻¹ = a - Real.sqrt (a ^ 2 - 1) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpectralRoot_inv ha

/--
[quantumIsingSpectralRoot_add_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma quantumIsingSpectralRoot_add_inv_eq
  {a : Real}
-- given
  (ha : 1 ≤ a) :
-- imply
  (quantumIsingSpectralRoot a + (quantumIsingSpectralRoot a)⁻¹) / 2 = a := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpectralRoot_add_inv ha

/--
[log_quantumIsingSpectralRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma log_quantumIsingSpectralRoot_eq
  {a : Real} :
-- imply
  Real.log (quantumIsingSpectralRoot a) = Real.arcosh a := by
-- proof
  apply StatMech.FrontierA.log_quantumIsingSpectralRoot a

/--
[sum_log_spectralParameter_sub_cos_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma sum_log_spectralParameter_sub_cos_antiperiodic_eq
  {n : Nat}
  {a : Real}
-- given
  (hn : n ≠ 0)
  (ha : 1 < a) :
-- imply
  (∑ j ∈ Finset.range n, Real.log (a - Real.cos (quantumIsingAntiperiodicAngle n j))) = -(n : Real) * Real.log 2 + (n : Real) * Real.arcosh a + 2 * Real.log (1 + (quantumIsingSpectralRoot a)⁻¹ ^ n) := by
-- proof
  apply StatMech.FrontierA.sum_log_spectralParameter_sub_cos_antiperiodic n hn a ha

/--
[sum_log_quantumIsingTrotterReducedParameter_sub_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicReduction.lean)
-/
@[path]
private lemma sum_log_quantumIsingTrotterReducedParameter_sub_cos_eq
  {n : Nat}
-- given
  (beta h k : Real)
  (hn : n ≠ 0)
  (ha : 1 < quantumIsingTrotterReducedParameter beta h n k) :
-- imply
  (∑ j ∈ Finset.range n, Real.log (quantumIsingTrotterReducedParameter beta h n k - Real.cos (quantumIsingAntiperiodicAngle n j))) = -(n : Real) * Real.log 2 + (n : Real) * Real.arcosh (quantumIsingTrotterReducedParameter beta h n k) + 2 * Real.log (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h n k))⁻¹ ^ n) := by
-- proof
  apply StatMech.FrontierA.sum_log_quantumIsingTrotterReducedParameter_sub_cos beta h k n hn ha


-- created on 2026-10-23
