import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBogoliubovLimit
open MeasureTheory StatMech StatMech.FrontierA


/--
[quantumIsing_radicand_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsing_radicand_nonneg_eq
-- given
  (h k : ℝ) :
-- imply
  0 ≤ 1 + 4 * h ^ 2 + 4 * h * Real.cos k := by
-- proof
  apply StatMech.FrontierA.quantumIsing_radicand_nonneg h k

/--
[continuous_quantumIsingDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma continuous_quantumIsingDispersion_eq
-- given
  (h : ℝ) :
-- imply
  Continuous (quantumIsingDispersion h) := by
-- proof
  apply StatMech.FrontierA.continuous_quantumIsingDispersion h

/--
[continuous_quantumIsingModeLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma continuous_quantumIsingModeLog_eq
-- given
  (beta h : ℝ) :
-- imply
  Continuous (quantumIsingModeLog beta h) := by
-- proof
  apply StatMech.FrontierA.continuous_quantumIsingModeLog beta h

/--
[periodic_quantumIsingDispersion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma periodic_quantumIsingDispersion_eq
-- given
  (h : ℝ) :
-- imply
  Function.Periodic (quantumIsingDispersion h) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_quantumIsingDispersion h

/--
[periodic_quantumIsingModeLog](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma periodic_quantumIsingModeLog_eq
-- given
  (beta h : ℝ) :
-- imply
  Function.Periodic (quantumIsingModeLog beta h) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_quantumIsingModeLog beta h

/--
[quantumIsingDispersion_neg_eq_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsingDispersion_neg_eq_shift_eq
-- given
  (h k : ℝ) :
-- imply
  quantumIsingDispersion (-h) k = quantumIsingDispersion h (k + Real.pi) := by
-- proof
  apply StatMech.FrontierA.quantumIsingDispersion_neg_eq_shift h k

/--
[quantumIsingModeLog_neg_eq_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsingModeLog_neg_eq_shift_eq
-- given
  (beta h k : ℝ) :
-- imply
  quantumIsingModeLog beta (-h) k = quantumIsingModeLog beta h (k + Real.pi) := by
-- proof
  apply StatMech.FrontierA.quantumIsingModeLog_neg_eq_shift beta h k

/--
[integral_quantumIsingModeLog_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma integral_quantumIsingModeLog_shift_eq
-- given
  (beta h : ℝ) :
-- imply
  (∫ k in (0 : ℝ)..(2 * Real.pi), quantumIsingModeLog beta h k) = ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
-- proof
  apply StatMech.FrontierA.integral_quantumIsingModeLog_shift beta h

/--
[integral_quantumIsingModeLog_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma integral_quantumIsingModeLog_neg_eq
-- given
  (beta h : ℝ) :
-- imply
  (∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta (-h) k) = ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k := by
-- proof
  apply StatMech.FrontierA.integral_quantumIsingModeLog_neg beta h

/--
[quantumIsingFreeEnergyValue_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsingFreeEnergyValue_neg_eq
-- given
  (beta h : ℝ) :
-- imply
  quantumIsingFreeEnergyValue beta (-h) = quantumIsingFreeEnergyValue beta h := by
-- proof
  apply StatMech.FrontierA.quantumIsingFreeEnergyValue_neg beta h

/--
[quantumIsingModeLog_average_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsingModeLog_average_tendsto_eq
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun L : ℕ => (1 / (L : ℝ)) * ∑ j ∈ Finset.range L, quantumIsingModeLog beta h (2 * Real.pi * j / L)) Filter.atTop (nhds ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, quantumIsingModeLog beta h k)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingModeLog_average_tendsto beta h

/--
[quantumIsingBogoliubovFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBogoliubovLimit.lean)
-/
@[path]
private lemma quantumIsingBogoliubovFreeEnergy_tendsto_eq
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (quantumIsingBogoliubovFreeEnergy beta h) Filter.atTop (nhds (quantumIsingFreeEnergyValue beta h)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBogoliubovFreeEnergy_tendsto beta h


-- created on 2026-10-23
