/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/LogExpBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Structure.StatisticalMechanics.Code.Exact3D.LogExpBounds

@[expose] public section


namespace StatMech

namespace Exact3D

abbrev RatExpUpperBound (q r : ℚ) : Prop :=
  ExpUpperBound (q : ℝ) (r : ℝ)


abbrev RatLogUpperBound (x u : ℚ) : Prop :=
  LogUpperBound (x : ℝ) (u : ℝ)


abbrev RatLogLowerBound (l x : ℚ) : Prop :=
  LogLowerBound (l : ℝ) (x : ℝ)

end Exact3D
end StatMech
