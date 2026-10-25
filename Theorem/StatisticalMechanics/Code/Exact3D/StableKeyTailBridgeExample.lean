/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/StableKeyTailBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyTailBridge.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.StableKeyCertificateExample.Part2
import Def.StatisticalMechanics.Code.Exact3D.StableKeyTailBridgeExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace BoundedPolymerCase

namespace StableKeyTailBridgeExample

theorem zeroSplit_additive {d : ℕ} (K : TailCutoff) :
    (zeroSplit (d := d) K).Additive := by
  intro a
  simp [zeroSplit]


theorem zeroSplit_total_zero_off_support {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    ∀ a, a ∉ support → (zeroSplit (d := d) K).totalContribution a = 0 := by
  intro a _
  rfl


theorem zeroSplit_tailEnvelopeOn {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (zeroSplit (d := d) K).TailEnvelopeOn support (fun _ => (0 : ℝ)) := by
  intro _ _
  simp [zeroSplit]


theorem zeroSplit_tailContribution_nonpos_off_support {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    ∀ a, a ∉ support → (zeroSplit (d := d) K).tailContribution a ≤ 0 := by
  intro _ _
  simp [zeroSplit]


theorem zeroSplit_total_nonneg {d : ℕ} (K : TailCutoff) :
    ∀ a, 0 ≤ (zeroSplit (d := d) K).totalContribution a := by
  intro _
  simp [zeroSplit]


theorem zero_tailEnvelope_sum_le {d : ℕ} (K : TailCutoff)
    (support : Finset (FiniteCutoffCoordinate d K)) :
    (∑ _a ∈ support, (0 : ℝ)) ≤ 0 := by
  simp


end StableKeyTailBridgeExample
end BoundedPolymerCase
end Exact3D
end StatMech
