/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part5
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

theorem singletonFiniteAsInfinite_prefixSum_eq_three :
    singletonFiniteAsInfinite.prefixSum = 3 := by
  norm_num [singletonFiniteAsInfinite, singletonFiniteCertificate,
    TailSummability.InfiniteTailCertificate.prefixSum]


theorem singletonFiniteAsInfinite_tsum_weight_le_three :
    (∑' n : ℕ, singletonFiniteAsInfinite.weight n) ≤ 3 := by
  have h :=
    singletonFiniteAsInfinite.tsum_weight_le_prefixSum_add_tailBound
  rw [singletonFiniteAsInfinite_prefixSum_eq_three] at h
  norm_num [singletonFiniteAsInfinite, singletonFiniteCertificate] at h ⊢

end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
