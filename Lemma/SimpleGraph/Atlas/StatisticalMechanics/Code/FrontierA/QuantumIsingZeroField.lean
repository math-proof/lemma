import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingZeroField.Part2
open Filter Matrix StatMech StatMech.FrontierA


/--
[transferSpin_quantumIsingBoolTransferEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma transferSpin_quantumIsingBoolTransferEquiv_eq
  {b : Bool} :
-- imply
  FrontierC.transferSpin (quantumIsingBoolTransferEquiv b) = quantumIsingSpinSign b := by
-- proof
  apply StatMech.FrontierA.transferSpin_quantumIsingBoolTransferEquiv b

/--
[quantumIsingConfigTransferEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingConfigTransferEquiv_apply_eq
  {L : Nat}
  {sigma : QuantumIsingChainConfig L}
  {i : Fin L} :
-- imply
  quantumIsingConfigTransferEquiv L sigma i = quantumIsingBoolTransferEquiv (sigma i) := by
-- proof
  apply StatMech.FrontierA.quantumIsingConfigTransferEquiv_apply L sigma i

/--
[quantumIsingBoltzmannGenerator_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingBoltzmannGenerator_zero_field_eq
  {beta : Real}
  {L : Nat} :
-- imply
  quantumIsingBoltzmannGenerator beta 0 L = Matrix.diagonal (fun sigma ↦ ((beta / 4 * quantumIsingChainInteraction L sigma : Real) : Complex)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingBoltzmannGenerator_zero_field beta L

/--
[quantumIsingQuantumPartition_zero_field_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_zero_field_sum_eq
  {beta : Real}
  {L : Nat} :
-- imply
  quantumIsingQuantumPartition beta 0 L = ∑ sigma : QuantumIsingChainConfig L, (Real.exp (beta / 4 * quantumIsingChainInteraction L sigma) : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_zero_field_sum beta L

/--
[quantumIsingChainInteraction_eq_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingChainInteraction_eq_transfer_eq
  {L : Nat}
  [NeZero L]
  {sigma : QuantumIsingChainConfig L} :
-- imply
  quantumIsingChainInteraction L sigma = ∑ i : Fin L, FrontierC.transferSpin (quantumIsingConfigTransferEquiv L sigma i) * FrontierC.transferSpin (quantumIsingConfigTransferEquiv L sigma (i + 1)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingChainInteraction_eq_transfer L sigma

/--
[isingRingExponent_configTransfer_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma isingRingExponent_configTransfer_zero_eq
  {beta : Real}
  {L : Nat}
  [NeZero L]
  {sigma : QuantumIsingChainConfig L} :
-- imply
  FrontierC.isingRingExponent (beta / 4) 0 (quantumIsingConfigTransferEquiv L sigma) = beta / 4 * quantumIsingChainInteraction L sigma := by
-- proof
  apply StatMech.FrontierA.isingRingExponent_configTransfer_zero beta L sigma

/--
[quantumIsingQuantumPartition_zero_field_eq_isingRingZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_zero_field_eq_isingRingZ_eq
  {beta : Real}
  {L : Nat}
  [NeZero L] :
-- imply
  quantumIsingQuantumPartition beta 0 L = (FrontierC.isingRingZ L (beta / 4) 0 : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_zero_field_eq_isingRingZ beta L

/--
[quantumIsingQuantumPartition_zero_field_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingQuantumPartition_zero_field_norm_eq
  {beta : Real}
  {L : Nat}
  [NeZero L] :
-- imply
  ‖quantumIsingQuantumPartition beta 0 L‖ = FrontierC.isingRingZ L (beta / 4) 0 := by
-- proof
  apply StatMech.FrontierA.quantumIsingQuantumPartition_zero_field_norm beta L

/--
[quantumIsingFiniteFreeEnergy_zero_field_eq_ringPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_zero_field_eq_ringPressure_eq
  {beta : Real}
  {n : Nat} :
-- imply
  quantumIsingFiniteFreeEnergy beta 0 (n + 1) = -(Real.log (FrontierC.isingRingZ (n + 1) (beta / 4) 0) / (n + 1 : Real)) / beta := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_zero_field_eq_ringPressure beta n

/--
[isingTransferEigenPlus_quarter_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma isingTransferEigenPlus_quarter_zero_eq
  {beta : Real} :
-- imply
  FrontierC.isingTransferEigenPlus (beta / 4) 0 = 2 * Real.cosh (beta / 4) := by
-- proof
  apply StatMech.FrontierA.isingTransferEigenPlus_quarter_zero beta

/--
[quantumIsingModeLog_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingModeLog_zero_eq
  {beta k : Real} :
-- imply
  quantumIsingModeLog beta 0 k = Real.log (Real.cosh (beta / 4)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingModeLog_zero beta k

/--
[quantumIsingFreeEnergyValue_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingFreeEnergyValue_zero_eq
  {beta : Real}
-- given
  (hbeta : beta ≠ 0) :
-- imply
  quantumIsingFreeEnergyValue beta 0 = -Real.log (2 * Real.cosh (beta / 4)) / beta := by
-- proof
  apply StatMech.FrontierA.quantumIsingFreeEnergyValue_zero beta hbeta

/--
[quantumIsingFiniteFreeEnergy_tendsto_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_tendsto_zero_field_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (quantumIsingFiniteFreeEnergy beta 0) atTop (nhds (quantumIsingFreeEnergyValue beta 0)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_tendsto_zero_field beta hbeta

/--
[quantumIsingFiniteFreeEnergy_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean)
-/
@[path]
private lemma quantumIsingFiniteFreeEnergy_tendsto_eq
-- given
  (beta h : Real)
  (hbeta : 0 < beta) :
-- imply
  Tendsto (quantumIsingFiniteFreeEnergy beta h) atTop (nhds (quantumIsingFreeEnergyValue beta h)) := by
-- proof
  apply StatMech.FrontierA.quantumIsingFiniteFreeEnergy_tendsto beta h hbeta


-- created on 2026-10-23
