/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part7


namespace StatMech

namespace Exact3D

namespace RatInterval

def vectorAdd {n : ℕ} (I J : IntervalVector n) : IntervalVector n :=
  fun i => add (I i) (J i)


def vectorNeg {n : ℕ} (I : IntervalVector n) : IntervalVector n :=
  fun i => neg (I i)


def vectorSub {n : ℕ} (I J : IntervalVector n) : IntervalVector n :=
  fun i => sub (I i) (J i)


end RatInterval
end Exact3D
end StatMech
