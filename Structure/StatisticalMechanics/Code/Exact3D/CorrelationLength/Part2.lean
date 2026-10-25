/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CorrelationLength.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Exact3D.CorrelationLength


namespace StatMech

namespace Exact3D

structure HasCorrelationLength {ι : Type*} (M : CriticalModel ι) (β : ℝ)
    (origin : ι) (ray : ℕ → ι) (ξ : ℝ) : Prop where
  xi_pos : 0 < ξ
  tendsto_inverse :
    HasInverseCorrelationLength M β origin ray ξ⁻¹


end Exact3D
end StatMech
