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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part18


namespace StatMech

namespace Exact3D

namespace FreeMassPowerLawToPlusAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ => freeSelectedSubcriticalMass_pos hmass hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  freeMass_scaling := hmass_scaling


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassPowerLawToPlusAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength :=
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  freeMass := freeSelectedPositiveSubcriticalMass hmass
  plus_free_agree := hagree
  freeMass_pos := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_pos hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  freeMass_realizes_inverse_length := fun _ hβ =>
    freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength hmass
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ) hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  massPrefactor := massPrefactor
  massPrefactor_pos := hmassPrefactor_pos
  massPrefactor_log_negligible := hmassPrefactor_log_negligible
  freeMass_scaling := hmass_scaling

end FreeMassPowerLawToPlusAnalyticRGToExponentTarget

namespace FreeAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toFreeLengthTarget


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toFreeLengthTarget


noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toFreeLengthTarget


noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toFreeLengthTarget

end FreeAnalyticRGToPlusExponentTarget

namespace FreeMassAnalyticRGToPlusExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toFreeMassTarget


noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    FreeMassAnalyticRGToPlusExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toFreeMassTarget

end FreeMassAnalyticRGToPlusExponentTarget

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreeSubcriticalCorrelationLengthBridge)
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
        freeSelectedSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeAnalyticRGToPlusExponentTarget.ofFreeCorrelationLengthBridge
    (C := C) hagree hbridge δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget


noncomputable def ofFreePositiveCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreePositiveSubcriticalCorrelationLengthBridge)
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
        freeSelectedPositiveSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeAnalyticRGToPlusExponentTarget.ofFreePositiveCorrelationLengthBridge
    (C := C) hagree hbridge δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusLengthTarget


noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusLengthTarget


noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusLengthTarget

end IsingAnalyticRGToExponentTarget

namespace IsingMassAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusMassTarget


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassAnalyticRGToPlusExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle prefactor hprefactor_pos
      hprefactor_log_negligible hscaling).toPlusMassTarget


noncomputable def ofFreeMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusMassTarget


noncomputable def ofFreePositiveMassPowerLawBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusMassTarget

end IsingMassAnalyticRGToExponentTarget

namespace IsingMassPowerLawAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
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
        freeSelectedSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreeMassBridge
    (C := C) hagree hmass δ hδ massPrefactor hmassPrefactor_pos
      hmassPrefactor_log_negligible hmass_scaling).toPlusMassPowerLawTarget


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
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
        freeSelectedPositiveSubcriticalMass hmass β =
          massPrefactor β *
            Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingMassPowerLawAnalyticRGToExponentTarget C :=
  (FreeMassPowerLawToPlusAnalyticRGToExponentTarget.ofFreePositiveMassBridge
    (C := C) hagree hmass δ hδ hδle massPrefactor
      hmassPrefactor_pos hmassPrefactor_log_negligible hmass_scaling).toPlusMassPowerLawTarget

end IsingMassPowerLawAnalyticRGToExponentTarget
end Exact3D
end StatMech
