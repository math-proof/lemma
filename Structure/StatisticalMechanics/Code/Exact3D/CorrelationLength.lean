/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech

namespace Exact3D

structure CriticalModel (ι : Type*) where
  
  betaC : ℝ
  

  twoPoint : ℝ → ι → ι → ℝ


end Exact3D
end StatMech
