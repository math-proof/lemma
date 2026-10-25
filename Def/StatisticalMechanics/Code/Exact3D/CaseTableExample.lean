/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CaseTableExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12


namespace StatMech

namespace Exact3D

namespace CaseTableExample

def boolTable : RatInterval.CaseTable Bool where
  cases := Finset.univ
  interval := fun b => if b then RatInterval.point 1 else RatInterval.point 0


def classify (b : Bool) : Bool :=
  b


def value (b : Bool) : ℝ :=
  if b then 1 else 0

end CaseTableExample
end Exact3D
end StatMech
