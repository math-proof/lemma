/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/PackageComparisonBridgeExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridge
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContractionExample.Part58
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailWitnessPackageExample.Part7
import Theorem.StatisticalMechanics.Code.Exact3D.PackageComparisonBridgeExample.Part4


namespace StatMech

namespace Exact3D

namespace PackageComparisonBridgeExample

open FiniteWitnessPackageExample

open FinitePlusTailContractionExample

open InfiniteTailWitnessPackageExample


noncomputable def doubledContributionSplitInfiniteTailCorrelationLength
    (β : ℝ) : ℝ :=
  2 * contributionSplitInfiniteTailCorrelationLength β


end PackageComparisonBridgeExample
end Exact3D
end StatMech
