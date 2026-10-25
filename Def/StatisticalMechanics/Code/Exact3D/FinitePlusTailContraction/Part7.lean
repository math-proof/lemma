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
import Instance.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part5
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace FinitePlusTailState

variable {n : ℕ} {α : Type*}

noncomputable def equivProduct :
    FinitePlusTailState n α ≃ FiniteContraction.L1Vector n × SummableTail α where
  toFun x := (FiniteContraction.L1Vector.ofFun x.finite, x.tail)
  invFun p := { finite := p.1.coord, tail := p.2 }
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro p
    cases p with
    | mk finite tail =>
        cases finite
        rfl


end FinitePlusTailState
end Exact3D
end StatMech
