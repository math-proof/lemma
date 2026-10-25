/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Structure.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part3


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

noncomputable def ofLinearStableRowSum {n : ℕ}
    (thermal : ℝ) (thermal_gt_one : 1 < thermal)
    (stableLinear : Fin n → Fin n → ℝ)
    {stableEnclosure : RatInterval.IntervalMatrix n n}
    (stable_enclosure_sound : RatInterval.MatrixMem stableLinear stableEnclosure)
    (stable_contraction : RatInterval.RowSumContraction stableEnclosure)
    (stable_dominated :
      (n : ℝ) * (stable_contraction.c : ℝ) ≤ |thermal|) :
    FiniteHyperbolicSplitting n where
  thermal := thermal
  thermal_gt_one := thermal_gt_one
  stable :=
    StableBlockWithRemainder.ofLinearRowSum stableLinear
      stable_enclosure_sound stable_contraction
  stable_dominated := by
    simpa [StableBlockWithRemainder.ofLinearRowSum_l1StepConstant] using
      stable_dominated


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
