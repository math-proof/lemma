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
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part11


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

noncomputable def splitting : FiniteHyperbolicSplitting 1 where
  thermal := 3
  thermal_gt_one := by norm_num
  stable := stableBlock
  stable_dominated := by
    rw [stableBlock_l1StepConstant]
    norm_num


noncomputable def splittingFromRowSum : FiniteHyperbolicSplitting 1 :=
  FiniteHyperbolicSplitting.ofLinearStableRowSum
    (n := 1) (thermal := 3) (by norm_num) stableLinear
    stableLinear_mem_enclosure stableRowSumContraction (by
      norm_num [stableRowSumContraction])


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
