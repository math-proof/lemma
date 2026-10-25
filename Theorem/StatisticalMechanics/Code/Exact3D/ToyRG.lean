/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part2


namespace StatMech

namespace Exact3D

theorem toyCertificate_predictedExponent_eq (scale : BlockScale)
    {thermalEigenvalue : ℝ} (hthermal : 1 < thermalEigenvalue) :
    (toyCertificate scale hthermal).predictedExponent =
      Real.log scale.toReal / Real.log thermalEigenvalue := by
  rfl


end Exact3D
end StatMech
