/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingAnalyticBridgeTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.AnalyticBridgeTarget.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part17
import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge


namespace StatMech

namespace Exact3D

theorem eventually_mem_isingLeftCriticalIoo {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3) := by
  filter_upwards
    [Ioo_mem_nhdsLT (show Ising.betaC 3 - δ < Ising.betaC 3 by
      linarith)] with β hβ
  exact hβ


theorem betaC_sub_pos_of_mem_isingLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < Ising.betaC 3 - β :=
  sub_pos.mpr hβ.2


theorem betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo
    {δ β : ℝ}
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    Ising.betaC 3 - β < δ := by
  linarith [hβ.1]


theorem beta_pos_of_mem_isingLeftCriticalIoo_of_delta_le_betaC
    {δ β : ℝ} (hδle : δ ≤ Ising.betaC 3)
    (hβ : β ∈ Set.Ioo (Ising.betaC 3 - δ) (Ising.betaC 3)) :
    0 < β := by
  have hnonneg : 0 ≤ Ising.betaC 3 - δ := sub_nonneg.mpr hδle
  linarith [hβ.1, hnonneg]


theorem eventually_betaC_sub_pos_isingLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      0 < Ising.betaC 3 - β := by
  filter_upwards [eventually_mem_isingLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_pos_of_mem_isingLeftCriticalIoo hβ


theorem eventually_betaC_sub_lt_delta_isingLeftCriticalIoo {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)),
      Ising.betaC 3 - β < δ := by
  filter_upwards [eventually_mem_isingLeftCriticalIoo hδ] with β hβ
  exact betaC_sub_lt_delta_of_mem_isingLeftCriticalIoo hβ


end Exact3D
end StatMech
