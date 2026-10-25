/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Theorem.StatisticalMechanics.Code.Exact3D.RG


namespace StatMech

namespace Exact3D

structure EffectiveHamiltonian where
  carrier : Type


structure BlockSpinMap (H : EffectiveHamiltonian) where
  scale : BlockScale
  map : H.carrier → H.carrier


structure RGFixedPointData (H : EffectiveHamiltonian) (R : BlockSpinMap H) where
  fixedPoint : H.carrier
  fixedPoint_eq : R.map fixedPoint = fixedPoint
  thermalEigenvalue : ℝ
  thermal_gt_one : 1 < thermalEigenvalue


end Exact3D
end StatMech
