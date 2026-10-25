/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part13


namespace StatMech

namespace Exact3D

theorem plusSelectedSubcriticalCorrelationLengthFromMass_pos
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < plusSelectedSubcriticalCorrelationLengthFromMass h β := by
  unfold plusSelectedSubcriticalCorrelationLengthFromMass
  exact inv_pos.mpr (plusSelectedSubcriticalMass_pos h hβ)


theorem plusSelectedSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedSubcriticalCorrelationLengthFromMass h β) := by
  unfold plusSelectedSubcriticalCorrelationLengthFromMass
  exact
    (plusSelectedSubcriticalMass_hasInverseCorrelationLength h hβ).hasCorrelationLength_inv
      (plusSelectedSubcriticalMass_pos h hβ)


end Exact3D
end StatMech
