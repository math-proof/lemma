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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

def geometricHalfInfiniteTailCertificate :
    InfiniteTailCertificate ℕ where
  finitePrefix := ∅
  weight := geometricHalfTailWeight
  prefixWeight := fun _ => 0
  tailWeight := geometricHalfTailWeight
  tailBound := 1
  prefix_eq_weight_on_prefix := by
    intro _ ha
    simp at ha
  prefixWeight_zero_off_prefix := by
    intro _ _
    rfl
  tailWeight_zero_on_prefix := by
    intro _ ha
    simp at ha
  decomposition := by
    intro n
    simp
  prefixWeight_nonneg := by
    intro _
    norm_num
  tailWeight_nonneg := geometricHalfTailWeight_nonneg
  summable_tail := geometricHalfTailWeight_summable
  tail_tsum_le := by
    rw [geometricHalfTailWeight_tsum_eq_one]


def geometricHalfInfiniteTailCertificateFromEnvelope :
    InfiniteTailCertificate ℕ :=
  InfiniteTailCertificate.of_tailEnvelope
    (∅ : Finset ℕ)
    geometricHalfTailWeight
    geometricHalfTailWeight
    geometricHalfTailWeight_nonneg
    geometricHalfTailWeight_nonneg
    (by
      intro _ _
      rfl)
    geometricHalfTailWeight_summable
    (by
      rw [geometricHalfTailWeight_tsum_eq_one])


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
