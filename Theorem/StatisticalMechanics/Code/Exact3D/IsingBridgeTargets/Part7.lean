/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part7


namespace StatMech

namespace Exact3D

theorem plusSelectedPositiveSubcriticalCorrelationLengthFromMass_pos
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β := by
  unfold plusSelectedPositiveSubcriticalCorrelationLengthFromMass
  exact inv_pos.mpr
    (plusSelectedPositiveSubcriticalMass_pos h hβpos hβc)


theorem
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
  unfold plusSelectedPositiveSubcriticalCorrelationLengthFromMass
  exact
    HasInverseCorrelationLength.hasCorrelationLength_inv
      (plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
        h hβpos hβc)
      (plusSelectedPositiveSubcriticalMass_pos h hβpos hβc)


end Exact3D
end StatMech
