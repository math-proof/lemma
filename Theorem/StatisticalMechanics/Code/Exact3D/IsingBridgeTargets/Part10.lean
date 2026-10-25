/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part10


namespace StatMech

namespace Exact3D

theorem plusSelectedPositiveSubcriticalCorrelationLength_spec
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < plusSelectedPositiveSubcriticalCorrelationLength h β ∧
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedPositiveSubcriticalCorrelationLength h β) := by
  unfold plusSelectedPositiveSubcriticalCorrelationLength
  rw [dif_pos hβpos, dif_pos hβc]
  exact Classical.choose_spec (h β hβpos hβc)


theorem plusSelectedPositiveSubcriticalCorrelationLength_pos
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    0 < plusSelectedPositiveSubcriticalCorrelationLength h β :=
  (plusSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc).1


theorem plusSelectedPositiveSubcriticalCorrelationLength_hasCorrelationLength
    (h : PlusPositiveSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβpos : 0 < β) (hβc : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedPositiveSubcriticalCorrelationLength h β) :=
  (plusSelectedPositiveSubcriticalCorrelationLength_spec h hβpos hβc).2


end Exact3D
end StatMech
