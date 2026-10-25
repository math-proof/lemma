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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part6


namespace StatMech

namespace Exact3D

namespace IsingMassAnalyticRGToExponentTarget

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
    IsingMassAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLengthFromMass hmass
  mass := plusSelectedSubcriticalMass hmass
  mass_pos := fun _ hβ => plusSelectedSubcriticalMass_pos hmass hβ.2
  mass_realizes_inverse_length := fun _ hβ =>
    plusSelectedSubcriticalMass_hasInverseCorrelationLength hmass hβ.2
  correlationLength_eq_inv_mass := fun _ _ => rfl
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling


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
    IsingMassAnalyticRGToExponentTarget C where
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
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end IsingMassAnalyticRGToExponentTarget
end Exact3D
end StatMech
