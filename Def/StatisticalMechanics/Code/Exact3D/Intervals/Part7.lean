/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Exact3D.Intervals.Part2


namespace StatMech

namespace Exact3D

namespace RatInterval

def VectorMem {n : ℕ} (x : Fin n → ℝ) (I : IntervalVector n) : Prop :=
  ∀ i, (I i).MemR (x i)


def VectorMemQ {n : ℕ} (x : Fin n → ℚ) (I : IntervalVector n) : Prop :=
  ∀ i, (I i).MemQ (x i)


def VectorNonnegative {n : ℕ} (I : IntervalVector n) : Prop :=
  ∀ i, (I i).Nonnegative


end RatInterval
end Exact3D
end StatMech
