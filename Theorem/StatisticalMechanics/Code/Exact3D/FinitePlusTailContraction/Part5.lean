/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Instance.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part2
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


theorem isometry_toLpOne :
    Isometry (toLpOne : SummableTail α → lp (fun _ : α => ℝ) (1 : ENNReal)) := by
  apply Isometry.of_dist_eq
  intro u v
  simpa using dist_toLpOne u v


theorem isUniformEmbedding_equivLpOne :
    IsUniformEmbedding
      (equivLpOne : SummableTail α ≃ lp (fun _ : α => ℝ) (1 : ENNReal)) :=
  isometry_toLpOne.isUniformEmbedding


end SummableTail
end Exact3D
end StatMech
