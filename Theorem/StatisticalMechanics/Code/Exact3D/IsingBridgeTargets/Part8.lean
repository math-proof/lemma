/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part8


namespace StatMech

namespace Exact3D

theorem freeSelectedPositiveSubcriticalMass_spec
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < freeSelectedPositiveSubcriticalMass h β ∧
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) := by
  unfold freeSelectedPositiveSubcriticalMass
  rw [dif_pos hβpos, dif_pos hβc]
  exact Classical.choose_spec (h β hβpos hβc)


theorem freeSelectedPositiveSubcriticalMass_pos
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < freeSelectedPositiveSubcriticalMass h β :=
  (freeSelectedPositiveSubcriticalMass_spec h hβpos hβc).1


theorem freeSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
    (h : FreePositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay (freeSelectedPositiveSubcriticalMass h β) :=
  (freeSelectedPositiveSubcriticalMass_spec h hβpos hβc).2


end Exact3D
end StatMech
