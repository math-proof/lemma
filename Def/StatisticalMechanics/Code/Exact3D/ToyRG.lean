/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ToyRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6


namespace StatMech

namespace Exact3D

noncomputable def ToyCriticalModel (_scale : BlockScale) (_thermalEigenvalue : ℝ) :
    CriticalModel Unit where
  betaC := 0
  twoPoint := fun _ _ _ => 0


end Exact3D
end StatMech
