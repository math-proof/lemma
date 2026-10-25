/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part5


namespace StatMech

namespace Exact3D

namespace RatInterval

def MatrixUpperRowSum {m n : ℕ} (I : IntervalMatrix m n) (i : Fin m) : ℚ :=
  ∑ j, (I i j).upper


def MatrixAbsRowSum {m n : ℕ} (I : IntervalMatrix m n) (i : Fin m) : ℚ :=
  ∑ j, (I i j).absUpper


def MatrixAbsColSum {m n : ℕ} (I : IntervalMatrix m n) (j : Fin n) : ℚ :=
  ∑ i, (I i j).absUpper


end RatInterval
end Exact3D
end StatMech
