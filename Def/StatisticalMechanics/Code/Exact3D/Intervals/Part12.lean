/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.StatisticalMechanics.Code.Exact3D.Intervals.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

def CaseTable.Covers {Case α : Type*} [DecidableEq Case]
    (T : CaseTable Case) (classify : α → Case) : Prop :=
  ∀ a, classify a ∈ T.cases


def CaseTable.Sound {Case α : Type*} [DecidableEq Case]
    (T : CaseTable Case) (classify : α → Case) (value : α → ℝ) : Prop :=
  ∀ a, (T.interval (classify a)).MemR (value a)

end RatInterval
end Exact3D
end StatMech
