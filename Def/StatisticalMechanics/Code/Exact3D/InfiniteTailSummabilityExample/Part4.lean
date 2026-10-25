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
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummabilityExample.Part3
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace InfiniteTailSummabilityExample

open TailSummability

noncomputable section

def geometricHalfInfiniteTailCertificateFromMaskedEnvelope :
    InfiniteTailCertificate ℕ :=
  InfiniteTailCertificate.of_masked_tailEnvelope
    ({0} : Finset ℕ)
    geometricHalfTailWeight
    geometricHalfTailWeight
    geometricHalfTailWeight_nonneg
    (by
      intro n _
      exact geometricHalfTailWeight_nonneg n)
    (by
      intro _ _
      exact le_rfl)
    (by
      refine maskedGeometricHalfTailWeight_summable.congr ?_
      intro n
      simp [maskedGeometricHalfTailWeight])
    (by
      convert maskedGeometricHalfTailWeight_tsum_le_one using 1)


end
end InfiniteTailSummabilityExample
end Exact3D
end StatMech
