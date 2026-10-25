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
import Def.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part12


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplittingExample

theorem stableBlock_linear_contraction_c :
    stableBlock.linear_contraction.c = (1 / 2 : ℚ) := by
  rfl


theorem stableBlock_remainder_lipschitz_upper :
    stableBlock.remainder_lipschitz.upper = 0 := by
  rfl


theorem stableBlock_l1StepConstant :
    stableBlock.l1StepConstant = (1 : ℝ) / 2 := by
  simp [StableBlockWithRemainder.l1StepConstant,
    StableBlockWithRemainder.coordinateConstant,
    stableBlock_linear_contraction_c,
    stableBlock_remainder_lipschitz_upper]


end FiniteHyperbolicSplittingExample
end Exact3D
end StatMech
