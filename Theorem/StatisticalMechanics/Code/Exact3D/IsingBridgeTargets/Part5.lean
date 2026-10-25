/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part5


namespace StatMech

namespace Exact3D

theorem plusPositiveSubcriticalMassBridge_of_subcriticalMassBridge
    (h : PlusSubcriticalMassBridge) :
    PlusPositiveSubcriticalMassBridge := by
  intro β _ hβc
  exact h β hβc


theorem freePositiveSubcriticalMassBridge_of_subcriticalMassBridge
    (h : FreeSubcriticalMassBridge) :
    FreePositiveSubcriticalMassBridge := by
  intro β _ hβc
  exact h β hβc


theorem plusPositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge
    (h : PlusSubcriticalCorrelationLengthBridge) :
    PlusPositiveSubcriticalCorrelationLengthBridge := by
  intro β _ hβc
  exact h β hβc


theorem freePositiveSubcriticalCorrelationLengthBridge_of_subcriticalBridge
    (h : FreeSubcriticalCorrelationLengthBridge) :
    FreePositiveSubcriticalCorrelationLengthBridge := by
  intro β _ hβc
  exact h β hβc


theorem plusPositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (hmass : PlusPositiveSubcriticalMassBridge) :
    PlusPositiveSubcriticalCorrelationLengthBridge := by
  intro β hβpos hβc
  obtain ⟨m, hm, hlen⟩ := hmass β hβpos hβc
  exact ⟨m⁻¹, inv_pos.mpr hm, hlen.hasCorrelationLength_inv hm⟩


theorem freePositiveSubcriticalCorrelationLengthBridge_of_massBridge
    (hmass : FreePositiveSubcriticalMassBridge) :
    FreePositiveSubcriticalCorrelationLengthBridge := by
  intro β hβpos hβc
  obtain ⟨m, hm, hlen⟩ := hmass β hβpos hβc
  exact ⟨m⁻¹, inv_pos.mpr hm, hlen.hasCorrelationLength_inv hm⟩


end Exact3D
end StatMech
