/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part14


namespace StatMech

namespace Exact3D

theorem freeSelectedSubcriticalMass_spec
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < freeSelectedSubcriticalMass h β ∧
      HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
        ising3DXAxisRay (freeSelectedSubcriticalMass h β) := by
  unfold freeSelectedSubcriticalMass
  rw [dif_pos hβ]
  exact Classical.choose_spec (h β hβ)


theorem freeSelectedSubcriticalMass_pos
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < freeSelectedSubcriticalMass h β :=
  (freeSelectedSubcriticalMass_spec h hβ).1


theorem freeSelectedSubcriticalMass_hasInverseCorrelationLength
    (h : FreeSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DFreeModel β ising3DOrigin
      ising3DXAxisRay (freeSelectedSubcriticalMass h β) :=
  (freeSelectedSubcriticalMass_spec h hβ).2


end Exact3D
end StatMech
