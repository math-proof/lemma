/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets


namespace StatMech

namespace Exact3D

theorem PlusXAxisFKConnectionAgrees.congr_eventually
    {β : ℝ} {conn comparison : ℕ → ℝ}
    (hcmp : PlusXAxisFKConnectionAgrees β conn)
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    PlusXAxisFKConnectionAgrees β comparison := by
  filter_upwards [hcmp, hEq] with n hcmp_n hEq_n
  exact hcmp_n.trans hEq_n.symm


theorem PlusXAxisFKConnectionAgrees.congr_eventually_iff
    {β : ℝ} {conn comparison : ℕ → ℝ}
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    PlusXAxisFKConnectionAgrees β conn ↔
      PlusXAxisFKConnectionAgrees β comparison :=
  ⟨fun hcmp => hcmp.congr_eventually hEq,
    fun hcmp => hcmp.congr_eventually
      (hEq.mono fun _ hn => hn.symm)⟩


theorem FreeXAxisFKConnectionAgrees.congr_eventually
    {β : ℝ} {conn comparison : ℕ → ℝ}
    (hcmp : FreeXAxisFKConnectionAgrees β conn)
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FreeXAxisFKConnectionAgrees β comparison := by
  filter_upwards [hcmp, hEq] with n hcmp_n hEq_n
  exact hcmp_n.trans hEq_n.symm


theorem FreeXAxisFKConnectionAgrees.congr_eventually_iff
    {β : ℝ} {conn comparison : ℕ → ℝ}
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FreeXAxisFKConnectionAgrees β conn ↔
      FreeXAxisFKConnectionAgrees β comparison :=
  ⟨fun hcmp => hcmp.congr_eventually hEq,
    fun hcmp => hcmp.congr_eventually
      (hEq.mono fun _ hn => hn.symm)⟩


end Exact3D
end StatMech
