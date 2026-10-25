/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
import Def.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets.Part3


namespace StatMech

namespace Exact3D

theorem FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually
    {conn comparison A : ℕ → ℝ} {m : ℝ}
    (hdecay : FKXAxisConnectionSubexponentialPrefactorDecay conn A m)
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FKXAxisConnectionSubexponentialPrefactorDecay comparison A m := by
  refine ⟨hdecay.1, hdecay.2.1, ?_⟩
  filter_upwards [hdecay.2.2, hEq] with n hdecay_n hEq_n
  rw [hEq_n]
  exact hdecay_n


theorem FKXAxisConnectionSubexponentialPrefactorDecay.congr_eventually_iff
    {conn comparison A : ℕ → ℝ} {m : ℝ}
    (hEq : ∀ᶠ n in Filter.atTop, comparison n = conn n) :
    FKXAxisConnectionSubexponentialPrefactorDecay conn A m ↔
      FKXAxisConnectionSubexponentialPrefactorDecay comparison A m :=
  ⟨fun hdecay => hdecay.congr_eventually hEq,
    fun hdecay => hdecay.congr_eventually
      (hEq.mono fun _ hn => hn.symm)⟩


end Exact3D
end StatMech
