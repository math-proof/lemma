/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part6


namespace StatMech

namespace Exact3D

namespace RatInterval

abbrev IntervalVector (n : ℕ) : Type :=
  Fin n → RatInterval


end RatInterval
end Exact3D
end StatMech
