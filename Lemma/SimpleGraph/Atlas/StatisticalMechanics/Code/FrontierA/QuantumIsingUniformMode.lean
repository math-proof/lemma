import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingUniformMode.Part5
open Filter Set StatMech StatMech.FrontierA


/--
[quantumIsingRapidityCorrection_eq_cosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingRapidityCorrection_eq_cosh_eq
  {x : Real} :
-- imply
  quantumIsingRapidityCorrection x = 2 * Real.log 2 + 2 * Real.log (Real.cosh (x / 2)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingRapidityCorrection_eq_cosh x

/--
[quantumIsingRapidityCorrection_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingRapidityCorrection_hasDerivAt_eq
  {x : Real} :
-- imply
  HasDerivAt quantumIsingRapidityCorrection (Real.tanh (x / 2)) x := by
-- proof
  apply StatMech.FrontierA.quantumIsingRapidityCorrection_hasDerivAt x

/--
[quantumIsingRapidityCorrection_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingRapidityCorrection_lipschitz_eq :
-- imply
  LipschitzWith 1 quantumIsingRapidityCorrection := by
-- proof
  apply StatMech.FrontierA.quantumIsingRapidityCorrection_lipschitz

/--
[quantumIsingModeScalarNormalization_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingModeScalarNormalization_tendsto_zero_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingModeScalarNormalization beta h) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.quantumIsingModeScalarNormalization_tendsto_zero beta h hbeta hh

/--
[quantumIsingShiftedTrotterModeContribution_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingShiftedTrotterModeContribution_tendstoUniformly_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (quantumIsingShiftedTrotterModeContribution beta h) (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingShiftedTrotterModeContribution_tendstoUniformly beta h hbeta hh

/--
[quantumIsingTrotterModeContribution_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingTrotterModeContribution_succ_eq
  {n : Nat}
  {k : Real}
-- given
  (beta h : Real) :
-- imply
  quantumIsingTrotterModeContribution beta h (n + 1) k = quantumIsingShiftedTrotterModeContribution beta h n k := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterModeContribution_succ beta h n k

/--
[quantumIsingTrotterModeContribution_tendstoUniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingTrotterModeContribution_tendstoUniformly_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  TendstoUniformly (quantumIsingTrotterModeContribution beta h) (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) atTop := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterModeContribution_tendstoUniformly beta h hbeta hh

/--
[continuous_quantumIsingTrotterModeLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma continuous_quantumIsingTrotterModeLimit_eq
-- given
  (beta h : Real) :
-- imply
  Continuous (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) := by
-- proof
  apply StatMech.FrontierA.continuous_quantumIsingTrotterModeLimit beta h

/--
[periodic_quantumIsingTrotterModeLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma periodic_quantumIsingTrotterModeLimit_eq
-- given
  (beta h : Real) :
-- imply
  Function.Periodic (fun k ↦ 2 * Real.log 2 + 2 * quantumIsingModeLog beta h k) (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierA.periodic_quantumIsingTrotterModeLimit beta h

/--
[quantumIsingTrotterModeContribution_midpoint_average_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingTrotterModeContribution_midpoint_average_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun L : Nat ↦ (1 / (L : Real)) * ∑ k ∈ Finset.range L, quantumIsingTrotterModeContribution beta h L (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi)) atTop (nhds ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterModeContribution_midpoint_average_tendsto beta h hbeta hh

/--
[quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh_eq
  {A : Real}
  {L : Nat}
-- given
  (hA : 1 ≤ A) :
-- imply
  (quantumIsingSpectralRoot A)⁻¹ ^ L = Real.exp (-(L : Real) * Real.arcosh A) := by
-- proof
  apply StatMech.FrontierA.quantumIsingSpectralRoot_inv_pow_eq_exp_neg_arcosh hA L

/--
[quantumIsingTrotterModeContribution_eq_spectralRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingTrotterModeContribution_eq_spectralRoot_eq
  {L : Nat}
  [Fact (2 < L)]
  {k : Real}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingTrotterModeContribution beta h L k = (L : Real) * Real.log (1 - (beta * h / (2 * L)) ^ 2) + (L : Real) * Real.arcosh (quantumIsingTrotterReducedParameter beta h L k) + 2 * Real.log (1 + (quantumIsingSpectralRoot (quantumIsingTrotterReducedParameter beta h L k))⁻¹ ^ L) := by
-- proof
  apply StatMech.FrontierA.quantumIsingTrotterModeContribution_eq_spectralRoot beta h L hbeta hh hx1 k

/--
[two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  (2 * Real.log ‖quantumIsingNormalizedSpinSector beta h L 1 1‖) / L = (1 / (L : Real)) * ∑ k ∈ Finset.range L, quantumIsingTrotterModeContribution beta h L (2 * Real.pi * (k + (1 : Real) / 2) / L - Real.pi) := by
-- proof
  apply StatMech.FrontierA.two_mul_log_norm_quantumIsingNormalizedSpinSector_eleven_div_eq_modeAverage beta h L hbeta hh hx1

/--
[quantumIsingElevenSectorLogDensity_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingUniformMode.lean)
-/
@[path]
private lemma quantumIsingElevenSectorLogDensity_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (quantumIsingElevenSectorLogDensity beta h) atTop (nhds ((1 / (2 * Real.pi)) * ∫ k in (-Real.pi)..Real.pi, (2 * Real.log 2 + 2 * quantumIsingModeLog beta h k))) := by
-- proof
  apply StatMech.FrontierA.quantumIsingElevenSectorLogDensity_tendsto beta h hbeta hh


-- created on 2026-10-23
