import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicSectorLimit
open Filter StatMech StatMech.FrontierA


/--
[quantumIsingNormalizedSpinSector_a_one_sq_eq_spectralRootProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_a_one_sq_eq_spectralRootProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingNormalizedSpinSector beta h L a 1 ^ 2 = ∏ i ∈ Finset.range L, ((((1 - (beta * h / (2 * L)) ^ 2) * quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi))) ^ L * (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)))⁻¹ ^ L) ^ 2 : Real) : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_a_one_sq_eq_spectralRootProduct beta h L a hbeta hh hx1

/--
[two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean)
-/
@[path]
private lemma two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L a 1‖ = ∑ i ∈ Finset.range L, ((L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) + (L : Real) * Real.arcosh (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)) + 2 * Real.log (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L (2 * Real.pi * (i + (a.val : Real) / 2) / L - Real.pi)))⁻¹ ^ L)) := by
-- proof
  apply StatMech.FrontierA.two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one beta h L a hbeta hh hx1

/--
[two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean)
-/
@[path]
private lemma two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  (2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L a 1‖) / L = (1 / (L : Real)) * ∑ k ∈ Finset.range L, quantumIsingTrotterModeContribution beta h L (2 * Real.pi * (k + (a.val : Real) / 2) / L - Real.pi) := by
-- proof
  apply StatMech.FrontierA.two_mul_log_norm_quantumIsingNormalizedSpinSector_a_one_div_eq_modeAverage beta h L a hbeta hh hx1

/--
[quantumIsingZeroOneSectorLogDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicSectorLimit.lean)
-/
@[path]
private lemma quantumIsingZeroOneSectorLogDensity_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingZeroOneSectorLogDensity beta h) atTop (nhds ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingZeroOneSectorLogDensity_tendsto beta h hbeta hh


-- created on 2026-10-23
