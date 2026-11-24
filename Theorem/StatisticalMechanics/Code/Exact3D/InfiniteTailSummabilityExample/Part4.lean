module
public import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic
public import Def.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part4
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/InfiniteTailSummabilityExample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

theorem geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound :
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope.tailBound = 1 :=
  rfl


theorem
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tsum_weight_le_prefixSum_add_one :
    (∑' n : ℕ,
        geometricHalfInfiniteTailCertificateFromMaskedEnvelope.weight n) ≤
      geometricHalfInfiniteTailCertificateFromMaskedEnvelope.prefixSum + 1 := by
  simpa [geometricHalfInfiniteTailCertificateFromMaskedEnvelope_tailBound] using
    geometricHalfInfiniteTailCertificateFromMaskedEnvelope.tsum_weight_le_prefixSum_add_tailBound


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
