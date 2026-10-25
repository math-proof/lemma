/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part9


namespace StatMech

namespace Exact3D

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofPlusMassBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedSubcriticalMass hmass
  mass_pos := fun _ hβ => plusSelectedSubcriticalMass_pos hmass hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  mass_scaling := hmass_scaling


noncomputable def ofPlusPositiveMassBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedPositiveSubcriticalMass hmass
  mass_pos := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  mass_scaling := hmass_scaling

end IsingMassPowerLawAnalyticRGToExponentTarget

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofPlusMassBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toLengthTarget


noncomputable def ofPlusPositiveMassBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (prefactor : ℝ → ℝ)
    (hprefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < prefactor β)
    (hprefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (prefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hscaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toLengthTarget


noncomputable def ofPlusMassPowerLawBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toLengthTarget


noncomputable def ofPlusPositiveMassPowerLawBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toLengthTarget

end IsingAnalyticRGToExponentTarget

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofPlusMassPowerLawBridge
    (hmass : PlusSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusMassBridge
    (C := C) hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toMassTarget


noncomputable def ofPlusPositiveMassPowerLawBridge
    (hmass : PlusPositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (massPrefactor : ℝ → ℝ)
    (hmassPrefactor_pos :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        0 < massPrefactor β)
    (hmassPrefactor_log_negligible :
      Filter.Tendsto
        (fun β : ℝ => Real.log (massPrefactor β) /
          Real.log (Ising.betaC 3 - β))
        (nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3))) (nhds 0))
    (hmass_scaling :
      ∀ β, β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) →
        plusSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (IsingMassPowerLawAnalyticRGToExponentTarget.ofPlusPositiveMassBridge
    (C := C) hmass δ hδ hδle massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toMassTarget

end IsingMassAnalyticRGToExponentTarget
end Exact3D
end StatMech
