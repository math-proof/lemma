/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part9


namespace StatMech

namespace Exact3D

theorem freeSelectedPositiveSubcriticalCorrelationLengthFromMass_pos
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β := by
  unfold freeSelectedPositiveSubcriticalCorrelationLengthFromMass
  exact inv_pos.mpr
    (freeSelectedPositiveSubcriticalMass_pos h hβpos hβc)


theorem
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DFreeModel β ising3DOrigin ising3DXAxisRay
      (freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β) := by
  unfold freeSelectedPositiveSubcriticalCorrelationLengthFromMass
  exact
    HasInverseCorrelationLength.hasCorrelationLength_inv
      (freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
        h hβpos hβc)
      (freeSelectedPositiveSubcriticalMass_pos h hβpos hβc)


theorem
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    plusSelectedPositiveSubcriticalCorrelationLengthFromMass h β =
      liminfCorrelationLength Ising3DModel β ising3DOrigin
        ising3DXAxisRay :=
  (plusSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    h hβpos hβc).liminfCorrelationLength_eq.symm


theorem
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass_eq_liminfCorrelationLength
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    freeSelectedPositiveSubcriticalCorrelationLengthFromMass h β =
      liminfCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay :=
  (freeSelectedPositiveSubcriticalCorrelationLengthFromMass_hasCorrelationLength
    h hβpos hβc).liminfCorrelationLength_eq.symm


end Exact3D
end StatMech
