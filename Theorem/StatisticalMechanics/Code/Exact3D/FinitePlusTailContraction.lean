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
import Instance.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


@[simp] theorem zero_coeff (a : α) : (0 : SummableTail α).coeff a = 0 :=
  rfl

@[ext]
theorem ext {u v : SummableTail α} (h : u.coeff = v.coeff) : u = v := by
  cases u
  cases v
  cases h
  rfl


end SummableTail
end Exact3D
end StatMech
