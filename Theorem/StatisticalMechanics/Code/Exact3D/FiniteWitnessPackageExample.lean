/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

theorem exampleSplit_total_nonneg :
    ∀ a : Fin 2, 0 ≤ TailSummabilityExample.exampleSplit.totalContribution a := by
  intro a
  norm_num [TailSummabilityExample.exampleSplit]


end FiniteWitnessPackageExample
end Exact3D
end StatMech
