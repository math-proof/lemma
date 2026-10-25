/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part6


namespace StatMech

namespace Exact3D

theorem plusSelectedPositiveSubcriticalMass_spec
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < plusSelectedPositiveSubcriticalMass h β ∧
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedPositiveSubcriticalMass h β) := by
  unfold plusSelectedPositiveSubcriticalMass
  rw [dif_pos hβpos, dif_pos hβc]
  exact Classical.choose_spec (h β hβpos hβc)


theorem plusSelectedPositiveSubcriticalMass_pos
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < plusSelectedPositiveSubcriticalMass h β :=
  (plusSelectedPositiveSubcriticalMass_spec h hβpos hβc).1


theorem plusSelectedPositiveSubcriticalMass_hasInverseCorrelationLength
    (h : PlusPositiveSubcriticalMassBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedPositiveSubcriticalMass h β) :=
  (plusSelectedPositiveSubcriticalMass_spec h hβpos hβc).2


end Exact3D
end StatMech
