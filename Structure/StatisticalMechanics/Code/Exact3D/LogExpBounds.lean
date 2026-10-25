/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech

namespace Exact3D

structure ExpUpperBound (q r : ℝ) : Prop where
  bound : Real.exp q ≤ r


structure LogUpperBound (x u : ℝ) : Prop where
  x_pos : 0 < x
  bound : Real.log x ≤ u


structure LogLowerBound (l x : ℝ) : Prop where
  x_pos : 0 < x
  bound : l ≤ Real.log x


end Exact3D
end StatMech
