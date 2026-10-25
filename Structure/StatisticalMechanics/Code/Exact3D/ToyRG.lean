/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part3


namespace StatMech

namespace Exact3D

structure ToyStableCoordinate (stableEigenvalue : ℝ) : Prop where
  abs_lt_one : |stableEigenvalue| < 1


end Exact3D
end StatMech
