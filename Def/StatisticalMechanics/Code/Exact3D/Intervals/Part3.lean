/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

def add (I J : RatInterval) : RatInterval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  lower_le_upper := add_le_add I.lower_le_upper J.lower_le_upper


def neg (I : RatInterval) : RatInterval where
  lower := -I.upper
  upper := -I.lower
  lower_le_upper := neg_le_neg I.lower_le_upper


def sub (I J : RatInterval) : RatInterval :=
  add I (neg J)


def finsetSum {α : Type*} (s : Finset α) (I : α → RatInterval) : RatInterval where
  lower := s.sum fun a => (I a).lower
  upper := s.sum fun a => (I a).upper
  lower_le_upper := by
    exact Finset.sum_le_sum fun a _ => (I a).lower_le_upper


def Nonnegative (I : RatInterval) : Prop :=
  0 ≤ I.lower


def absUpper (I : RatInterval) : ℚ :=
  max (-I.lower) I.upper

end RatInterval
end Exact3D
end StatMech
