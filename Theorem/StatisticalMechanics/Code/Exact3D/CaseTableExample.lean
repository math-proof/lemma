/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CaseTableExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Def.StatisticalMechanics.Code.Exact3D.CaseTableExample


namespace StatMech

namespace Exact3D

namespace CaseTableExample

theorem boolTable_covers :
    RatInterval.CaseTable.Covers boolTable classify := by
  intro b
  simp [boolTable, classify]

theorem boolTable_sound :
    RatInterval.CaseTable.Sound boolTable classify value := by
  intro b
  cases b <;> simp [boolTable, classify, value, RatInterval.MemR, RatInterval.point]

end CaseTableExample
end Exact3D
end StatMech
