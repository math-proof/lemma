/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.FKAnalyticBridgeTarget.Part3


namespace StatMech

namespace Exact3D

namespace FKToIsingAnalyticRGToExponentTarget

variable {C : RGCertificate Ising3DModel}


noncomputable def ofFreeMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreeSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedSubcriticalCorrelationLengthFromMass hmass β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength := freeSelectedSubcriticalCorrelationLengthFromMass hmass
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    freeSelectedSubcriticalCorrelationLengthFromMass_hasPlusCorrelationLength_of_agree
      hagree hmass hβ.2
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq


noncomputable def ofFreePositiveMassBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hmass : FreePositiveSubcriticalMassBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength :=
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass hmass
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    plus_hasCorrelationLength_xAxis_of_free_agree hagree hβ.2
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
        hmass
        (beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC hδle hβ)
        hβ.2)
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq


noncomputable def ofFreePositiveCorrelationLengthBridge
    (hagree : PlusFreeTwoPointAgreeBelowBetaC)
    (hbridge : FreePositiveSubcriticalCorrelationLengthBridge)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ Ising.betaC 3)
    (fkCorrelationLength : ℝ → ℝ)
    (hfk :
      HasCriticalNu (ParameterModel (IsingFK.pOfBeta (Ising.betaC 3)))
        fkCorrelationLength C.predictedExponent)
    (hEq :
      ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
        freeSelectedPositiveSubcriticalCorrelationLength hbridge β =
          fkCorrelationLength (IsingFK.pOfBeta β)) :
    FKToIsingAnalyticRGToExponentTarget C where
  δ := δ
  δ_pos := hδ
  isingCorrelationLength := freeSelectedPositiveSubcriticalCorrelationLength hbridge
  fkCorrelationLength := fkCorrelationLength
  realizesXAxisLength := fun _ hβ =>
    freeSelectedPositiveSubcriticalCorrelationLength_hasPlusCorrelationLength_of_agree
      hagree hbridge
      (beta_pos_of_mem_fkBetaLeftCriticalIoo_of_delta_le_betaC hδle hβ)
      hβ.2
  fk_hasCriticalNu := hfk
  ising_fk_length_agree := hEq

end FKToIsingAnalyticRGToExponentTarget
end Exact3D
end StatMech
