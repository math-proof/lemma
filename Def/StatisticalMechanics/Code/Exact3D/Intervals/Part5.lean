/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.StatisticalMechanics.Code.Exact3D.Intervals


namespace StatMech

namespace Exact3D

namespace RatInterval

def MatrixMem {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).MemR (A i j)


def MatrixMemQ {m n : ℕ} (A : Fin m → Fin n → ℚ)
    (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).MemQ (A i j)


def MatrixNonnegative {m n : ℕ} (I : IntervalMatrix m n) : Prop :=
  ∀ i j, (I i j).Nonnegative


end RatInterval
end Exact3D
end StatMech
