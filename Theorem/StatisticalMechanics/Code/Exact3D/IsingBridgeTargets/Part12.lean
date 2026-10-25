/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part12


namespace StatMech

namespace Exact3D

theorem plusSelectedSubcriticalMass_spec
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < plusSelectedSubcriticalMass h β ∧
      HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
        (plusSelectedSubcriticalMass h β) := by
  unfold plusSelectedSubcriticalMass
  rw [dif_pos hβ]
  exact Classical.choose_spec (h β hβ)


theorem plusSelectedSubcriticalMass_pos
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    0 < plusSelectedSubcriticalMass h β :=
  (plusSelectedSubcriticalMass_spec h hβ).1


theorem plusSelectedSubcriticalMass_hasInverseCorrelationLength
    (h : PlusSubcriticalMassBridge) {β : ℝ} (hβ : β < Ising.betaC 3) :
    HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay
      (plusSelectedSubcriticalMass h β) :=
  (plusSelectedSubcriticalMass_spec h hβ).2


end Exact3D
end StatMech
