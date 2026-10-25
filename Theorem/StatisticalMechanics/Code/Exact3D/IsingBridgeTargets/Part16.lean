/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part16


namespace StatMech

namespace Exact3D

theorem plusSelectedSubcriticalCorrelationLength_spec
    (h : PlusSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    0 < plusSelectedSubcriticalCorrelationLength h β ∧
      HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalCorrelationLength h β) := by
  unfold plusSelectedSubcriticalCorrelationLength
  rw [dif_pos hβ]
  exact Classical.choose_spec (h β hβ)


theorem plusSelectedSubcriticalCorrelationLength_pos
    (h : PlusSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    0 < plusSelectedSubcriticalCorrelationLength h β :=
  (plusSelectedSubcriticalCorrelationLength_spec h hβ).1


theorem plusSelectedSubcriticalCorrelationLength_hasCorrelationLength
    (h : PlusSubcriticalCorrelationLengthBridge) {β : ℝ}
    (hβ : β < Ising.betaC 3) :
    HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedSubcriticalCorrelationLength h β) :=
  (plusSelectedSubcriticalCorrelationLength_spec h hβ).2


end Exact3D
end StatMech
