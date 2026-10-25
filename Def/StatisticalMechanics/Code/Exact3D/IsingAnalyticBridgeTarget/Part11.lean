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
import Theorem.StatisticalMechanics.Code.Exact3D.IsingAnalyticBridgeTarget.Part12


namespace StatMech

namespace Exact3D

namespace FreeAnalyticRGToPlusExponentTarget

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
    FreeAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedSubcriticalCorrelationLength hbridge
  plus_free_agree := hagree
  free_realizesXAxisLength := fun _ hβ =>
    freeSelectedSubcriticalCorrelationLength_hasCorrelationLength hbridge hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling


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
    FreeAnalyticRGToPlusExponentTarget C where
  δ := δ
  δ_pos := hδ
  correlationLength := freeSelectedPositiveSubcriticalCorrelationLength hbridge
  plus_free_agree := hagree
  free_realizesXAxisLength := fun _ hβ =>
    freeSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
      hbridge
      (beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  prefactor := prefactor
  prefactor_pos := hprefactor_pos
  prefactor_log_negligible := hprefactor_log_negligible
  length_scaling := hscaling

end FreeAnalyticRGToPlusExponentTarget
end Exact3D
end StatMech
