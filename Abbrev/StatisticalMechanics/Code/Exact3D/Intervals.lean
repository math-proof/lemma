module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Exact3D.Intervals.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Intervals.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

namespace RatInterval

abbrev IntervalMatrix (m n : ℕ) : Type :=
  Fin m → Fin n → RatInterval


end RatInterval
end Exact3D
end StatMech
