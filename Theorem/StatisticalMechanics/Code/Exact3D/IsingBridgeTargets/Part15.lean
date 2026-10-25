/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part15


namespace StatMech

namespace Exact3D

theorem freeSelectedSubcriticalCorrelationLengthFromMass_pos
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < freeSelectedSubcriticalCorrelationLengthFromMass h β := by
  unfold freeSelectedSubcriticalCorrelationLengthFromMass
  exact inv_pos.mpr (freeSelectedSubcriticalMass_pos h hβ)


theorem freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedSubcriticalCorrelationLengthFromMass h β) := by
  unfold freeSelectedSubcriticalCorrelationLengthFromMass
  exact
    (freeSelectedSubcriticalMass_hasInverseCorrelationLength h hβ).hasCorrelationLength_inv
      (freeSelectedSubcriticalMass_pos h hβ)


theorem
    plusSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    plusSelectedSubcriticalCorrelationLengthFromMass h β =
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay :=
  (plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    h hβ).liminfCorrelationLength_eq.symm


theorem
    freeSelectedSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    freeSelectedSubcriticalCorrelationLengthFromMass h β =
      liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay :=
  (freeSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    h hβ).liminfCorrelationLength_eq.symm


end Exact3D
end StatMech
