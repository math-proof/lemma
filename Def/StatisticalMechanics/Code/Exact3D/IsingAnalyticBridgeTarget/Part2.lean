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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace IsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofPlusCorrelationLengthBridge
    (hbridge : PlusSubcriticalCorrelationLengthBridge)
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
        plusSelectedSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedSubcriticalCorrelationLength hbridge
  realizesXAxisLength := fun _ hβ =>
    plusSelectedSubcriticalCorrelationLength_hasCorrelationLength hbridge hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling


noncomputable def ofPlusPositiveCorrelationLengthBridge
    (hbridge : PlusPositiveSubcriticalCorrelationLengthBridge)
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
        plusSelectedPositiveSubcriticalCorrelationLength hbridge β =
          prefactor β *
            Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β))) :
    IsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := plusSelectedPositiveSubcriticalCorrelationLength hbridge
  realizesXAxisLength := fun _ hβ =>
    plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      hbridge
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end IsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
