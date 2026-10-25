/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength.Part3
import Structure.StatisticalMechanics.Code.Exact3D.RG.Part2


namespace StatMech

namespace Exact3D

noncomputable def predictedNu (scale : BlockScale) (thermalEigenvalue : ℝ) : ℝ :=
  Real.log scale.toReal / Real.log thermalEigenvalue

end Exact3D
end StatMech
